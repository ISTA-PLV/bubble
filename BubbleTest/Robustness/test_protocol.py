"""Fast generator/harness checks. No Lean sweep is launched by these tests."""
import argparse
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

import generate
import sweep


def reference_search(metadata):
    """Independent executable specification of the ground sequential strategy.
    Used only after measurements, never to assist either tactic.
    """
    by_target = [[] for _ in range(metadata["resourceTargetPairs"])]
    for kind, index in metadata["ruleOrder"]:
        p, q = (index, index) if kind == "canonical" else metadata["conflictEdges"][index]
        by_target[q].append(p)
    stats = dict(nodes=0, choices=0, backtracks=0, candidateChecks=0)
    order = metadata["targetOrder"]
    def solve(index, available):
        stats["nodes"] += 1
        if index == len(order):
            return [] if not available else None
        for p in by_target[order[index]]:
            stats["candidateChecks"] += 1
            if p not in available:
                continue
            stats["choices"] += 1
            tail = solve(index + 1, available - {p})
            if tail is not None:
                return [p] + tail
            stats["backtracks"] += 1
        return None
    allocation = solve(0, set(range(len(order))))
    return allocation, stats


class GeneratorTests(unittest.TestCase):
    def test_enum_matrix_is_frozen_and_paired(self):
        for size in range(4, 31, 2):
            hashes = []
            for seed in range(3000, 3005):
                cases = [generate.build_case(propositions=size, density=.2, seed=seed, shuffle=r)
                         for r in range(5)]
                metadata = [generate.case_metadata(c) for c in cases]
                self.assertEqual(len({m["instanceHash"] for m in metadata}), 1)
                self.assertEqual(len({m["presentationHash"] for m in metadata}), 5)
                self.assertEqual(len({c.conflicts for c in cases}), 1)
                hashes.append(metadata[0]["instanceHash"])
                for case in cases:
                    a = generate.render_lean(case, tactic="ibubble")
                    b = generate.render_lean(case, tactic="inaive")
                    self.assertIn("robustness_timed ibubble noSimp maxDepth 100", a)
                    self.assertEqual(a.replace("ibubble noSimp maxDepth 100", "METHOD"),
                                     b.replace("robustness_timed inaive", "robustness_timed METHOD"))
                    self.assertNotIn("hCanon", a)
                    self.assertNotIn("hDecoy", a)
            # Small sizes can have fewer than five possible graphs (p4 has
            # no decoys at density .2); do not mislabel seeds as unique graphs.
            self.assertGreaterEqual(len(set(hashes)), 1)

    def test_rule_set_is_preserved_across_shuffles(self):
        for seed in range(5):
            cases = [generate.build_case(propositions=12, density=.2, seed=seed, shuffle=r)
                     for r in range(5)]
            expected = set(cases[0].rule_order)
            for case in cases:
                self.assertEqual(set(case.rule_order), expected)
                allocation, _ = reference_search(generate.case_metadata(case))
                self.assertEqual(allocation, list(case.target_order))

    def test_reference_backtracks_on_decoy(self):
        metadata = {"resourceTargetPairs": 2, "ruleOrder": [["decoy", 0], ["canonical", 0], ["canonical", 1]],
                    "conflictEdges": [[1, 0]], "targetOrder": [0, 1]}
        self.assertEqual(reference_search(metadata)[1]["backtracks"], 1)
        metadata["targetOrder"] = [1, 0]
        self.assertEqual(reference_search(metadata)[1]["backtracks"], 0)


class HarnessTests(unittest.TestCase):
    def setUp(self):
        sweep.STOP.clear()

    def tearDown(self):
        sweep.cancel_running()
        sweep.STOP.clear()

    def test_status_and_measurement_parsing(self):
        self.assertEqual(sweep._status("error: iseq: no resource allocation", False, 1), "search_exhausted")
        self.assertEqual(sweep.SEQ_STATS.findall("IOSEQ_STATS 4 3 1 4\n"), [("4", "3", "1", "4")])
        self.assertEqual(generate.TACTICS, ("ibubble", "inaive"))
        args = sweep.build_argument_parser().parse_args([])
        self.assertEqual(args.ibubble_sizes, list(range(4, 31, 2)))
        self.assertEqual(args.inaive_sizes, list(range(4, 17, 2)))
        self.assertEqual(args.tactics, ["ibubble", "inaive"])
        self.assertEqual(args.shuffles, 5)
        self.assertEqual(len(args.seeds), 5)
        self.assertEqual(args.out.name, "result")

    def test_resume_reuses_recorded_cases_without_manifest(self):
        with tempfile.TemporaryDirectory(prefix="bubble-resume-") as directory:
            root = Path(directory)
            results = root / "results.jsonl"
            rows = [{"tactic": tactic, "propositions": 4, "seed": 1,
                     "shuffle": 0, "density": .2, "status": "success",
                     "tacticSeconds": .1, "configHash": "historical-metadata"}
                    for tactic in generate.TACTICS]
            results.write_text("\n".join(map(json.dumps, rows)) + "\n")
            original = results.read_bytes()
            with mock.patch.object(sweep, "run_case") as run_case:
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(sweep.main([
                        "--out", directory, "--sizes", "4", "--seeds", "1",
                        "--shuffles", "1",
                    ]), 0)
                run_case.assert_not_called()
            self.assertEqual(results.read_bytes(), original)
            self.assertEqual(list(root.iterdir()), [results])

    def test_success_times_exclude_timeouts(self):
        rows = {("ibubble", 10, 1, 0): (.2, "success", .3),
                ("ibubble", 10, 1, 1): (.2, "tactic_timeout", 999)}
        with contextlib.redirect_stdout(io.StringIO()) as output:
            sweep.summarize(rows)
        self.assertNotIn("999", output.getvalue())

    def test_case_sidecars_are_temporary_and_failure_diagnostics_are_saved(self):
        with tempfile.TemporaryDirectory(prefix="bubble-cleanup-test-") as directory:
            root = Path(directory)
            args = sweep.build_argument_parser().parse_args(["--out", directory])
            paths = []
            for code in [0, 1]:
                def fake_process(command, **kwargs):
                    source = Path(command[-1])
                    self.assertTrue(source.is_file())
                    self.assertNotEqual(source.parent, root)
                    paths.append(source.parent)
                    kwargs["stdout"].write("time: 1ms\n" if code == 0 else "error: simulated failure\n")
                    Path(kwargs["env"]["BUBBLE_ROBUSTNESS_MARKERS"]).write_text(
                        "ROBUSTNESS_START\nROBUSTNESS_END 1000000 1\n")
                    process = mock.Mock()
                    process.poll.return_value = code
                    return process
                with mock.patch.object(sweep.subprocess, "Popen", side_effect=fake_process):
                    record = sweep.run_case("inaive", 4, 3000, 0, args)
                self.assertEqual(record["status"], "success" if code == 0 else "lean_error")
                self.assertIsNone(record["outputFile"])
                self.assertIsNone(record["timingFile"])
                self.assertEqual(record["diagnosticOutput"],
                                 None if code == 0 else "error: simulated failure\n")
                self.assertFalse(paths[-1].exists())
                self.assertEqual(list(root.iterdir()), [])

            def interrupted_case(*arguments):
                paths.append(arguments[-1])
                (paths[-1] / "case.timing").write_text("ROBUSTNESS_START\n")
                raise sweep.CancelledError()
            with mock.patch.object(sweep, "_run_case", side_effect=interrupted_case):
                with self.assertRaises(sweep.CancelledError):
                    sweep.run_case("inaive", 4, 3000, 0, args)
            self.assertFalse(paths[-1].exists())

    def test_wrapper_generates_only_png_and_checks_dependencies_first(self):
        with tempfile.TemporaryDirectory(prefix="bubble-wrapper-") as directory:
            root = Path(directory)
            calls_file = root / "calls.jsonl"
            fake_python = root / "python"
            fake_python.write_text(
                f"#!{sys.executable}\n"
                "import json, os, sys\n"
                "with open(os.environ['BUBBLE_TEST_CALLS'], 'a') as stream:\n"
                "    stream.write(json.dumps(sys.argv[1:]) + '\\n')\n"
                "sys.exit(1 if sys.argv[1] == '-c' and "
                "os.environ.get('BUBBLE_TEST_MISSING_DEPS') == '1' else 0)\n")
            fake_python.chmod(0o755)
            env = {**os.environ, "BUBBLE_PYTHON": str(fake_python),
                   "BUBBLE_PLOT_PYTHON": str(fake_python),
                   "BUBBLE_TEST_CALLS": str(calls_file), "BUBBLE_TEST_MISSING_DEPS": "0"}
            wrapper = Path(__file__).with_name("run_benchmark.sh")
            output = str(root / "result with spaces")
            command = ["bash", str(wrapper), "--out", output]
            subprocess.run(command, env=env, check=True, capture_output=True)
            calls = [json.loads(line) for line in calls_file.read_text().splitlines()]
            self.assertEqual([Path(call[0]).name for call in calls],
                             ["-c", "sweep.py", "plot.py"])
            self.assertEqual(calls[1][1:], ["--out", output])
            self.assertEqual(calls[2][1:],
                             [output, "--min-seeds", "1", "--out",
                              str(Path(output) / "architecture_comparison.png")])
            calls_file.write_text("")
            env["BUBBLE_TEST_MISSING_DEPS"] = "1"
            failed = subprocess.run(command, env=env, capture_output=True, text=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("no experiments were started", failed.stderr)
            calls = [json.loads(line) for line in calls_file.read_text().splitlines()]
            self.assertEqual(len(calls), 1)
            self.assertEqual(calls[0][0], "-c")
            calls_file.write_text("")
            subprocess.run(["bash", str(wrapper), "--help"], env=env,
                           check=True, capture_output=True)
            calls = [json.loads(line) for line in calls_file.read_text().splitlines()]
            self.assertEqual(len(calls), 1)
            self.assertEqual(Path(calls[0][0]).name, "sweep.py")
            self.assertEqual(calls[0][1:], ["--help"])

    def test_deadlines_kill_private_processes(self):
        scripts = [("", "startup_timeout"),
                   ("print('ROBUSTNESS_START');", "tactic_timeout"),
                   ("print('ROBUSTNESS_START');print('ROBUSTNESS_END 1 1');", "check_timeout")]
        for prefix, expected in scripts:
            with tempfile.TemporaryDirectory(prefix="bubble-deadline-") as directory:
                path = Path(directory) / "markers"
                args = argparse.Namespace(timeout_scope="tactic", timeout=.10,
                                          startup_timeout=.10, check_timeout=.10)
                with path.open("w") as output:
                    process = subprocess.Popen([sys.executable, "-u", "-c",
                                                "import time;" + prefix + "time.sleep(20)"],
                                               stdout=output, start_new_session=True)
                    try:
                        _, reason = sweep.wait_case(process, path, args, time.perf_counter())
                        self.assertEqual(reason, expected)
                        self.assertIsNotNone(process.poll())
                    finally:
                        sweep.kill_process(process)


if __name__ == "__main__":
    unittest.main()
