#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/../.." && pwd)"
runs="${1:-5}"
output_dir="${script_dir}/results"
log_dir="${output_dir}/logs"

tactic_table="${output_dir}/tactic_counts.txt"
tactic_csv="${output_dir}/tactic_counts.csv"
tactic_json="${output_dir}/tactic_counts.json"
build_runs_csv="${output_dir}/build_runs.csv"
build_summary_csv="${output_dir}/build_summary.csv"
search_runs_csv="${output_dir}/ibubble_runs.csv"
search_invocations_csv="${output_dir}/ibubble_invocations.csv"
search_files_csv="${output_dir}/ibubble_files.csv"
search_layers_csv="${output_dir}/ibubble_layers.csv"
elaboration_runs_csv="${output_dir}/ibubble_file_elaboration_runs.csv"
report_md="${output_dir}/README.md"

if ! [[ "${runs}" =~ ^[1-9][0-9]*$ ]]; then
  echo "usage: $0 [positive-number-of-runs]" >&2
  exit 2
fi

mkdir -p "${output_dir}" "${log_dir}"
cd "${repo_root}"

python3 "${script_dir}/count_tactics.py" > "${tactic_table}"
python3 "${script_dir}/count_tactics.py" --csv > "${tactic_csv}"
python3 "${script_dir}/count_tactics.py" --json > "${tactic_json}"

echo "Preparing shared dependencies and all three case-study variants..." >&2
if ! lake build BubbleTest.IrisITree BubbleTest.IrisITreeBubble BubbleTest.IrisITreeScript > "${log_dir}/warmup.log" 2>&1; then
  echo "Initial benchmark build failed; see ${log_dir}/warmup.log" >&2
  exit 1
fi

variant_stem() {
  case "$1" in
    manual) echo "IrisITree" ;;
    search) echo "IrisITreeBubble" ;;
    generated) echo "IrisITreeScript" ;;
    *) return 2 ;;
  esac
}

variant_target() {
  case "$1" in
    manual) echo "BubbleTest.IrisITree" ;;
    search) echo "BubbleTest.IrisITreeBubble" ;;
    generated) echo "BubbleTest.IrisITreeScript" ;;
    *) return 2 ;;
  esac
}

clean_variant_artifacts() {
  local stem="$1"
  local base
  for base in ".lake/build/lib/lean/BubbleTest" ".lake/build/ir/BubbleTest"; do
    if [[ -d "${base}" ]]; then
      rm -rf -- "${base}/${stem}"
      find "${base}" -maxdepth 1 -type f -name "${stem}.*" -delete
    fi
  done
}

measure_build() {
  local log="$1"
  local target="$2"
  python3 - "${log}" "${target}" <<'PY'
import pathlib
import subprocess
import sys
import time

log = pathlib.Path(sys.argv[1])
target = sys.argv[2]
started = time.perf_counter()
with log.open("w", encoding="utf-8") as stream:
    completed = subprocess.run(
        ["lake", "build", f"+{target}"],
        stdout=stream,
        stderr=subprocess.STDOUT,
        check=False,
    )
print(f"{(time.perf_counter() - started) * 1000:.6f}")
raise SystemExit(completed.returncode)
PY
}

if [[ ! -f "${build_runs_csv}" ]]; then
  printf 'variant,run,order,wall_ms\n' > "${build_runs_csv}"
fi
variants=(manual search generated)
for run in $(seq 1 "${runs}"); do
  offset=$(( (run - 1) % 3 ))
  for position in 0 1 2; do
    index=$(( (offset + position) % 3 ))
    variant="${variants[${index}]}"
    stem="$(variant_stem "${variant}")"
    target="$(variant_target "${variant}")"
    log="${log_dir}/build-${variant}-run-${run}.log"
    if awk -F, -v variant="${variant}" -v run="${run}" '
      NR > 1 && $1 == variant && $2 == run { found = 1 }
      END { exit !found }
    ' "${build_runs_csv}"; then
      echo "[build cached ${run}/${runs}] ${variant}" >&2
      continue
    fi
    echo "[build ${run}/${runs}, order $((position + 1))/3] ${variant}" >&2
    clean_variant_artifacts "${stem}"
    if ! wall_ms="$(measure_build "${log}" "${target}")"; then
      echo "Build failed for ${variant}; see ${log}" >&2
      exit 1
    fi
    printf '%s,%s,%s,%s\n' "${variant}" "${run}" "$((position + 1))" "${wall_ms}" >> "${build_runs_csv}"
  done
done

python3 - "${build_runs_csv}" "${build_summary_csv}" "${runs}" <<'PY'
import csv
import statistics
import sys

source, destination, requested_runs = sys.argv[1:]
requested_runs = int(requested_runs)
order = ("manual", "search", "generated")
samples = {variant: [] for variant in order}
with open(source, newline="", encoding="utf-8") as stream:
    for row in csv.DictReader(stream):
        if int(row["run"]) <= requested_runs:
            samples[row["variant"]].append(float(row["wall_ms"]))

with open(destination, "w", newline="", encoding="utf-8") as stream:
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow(("variant", "runs", "mean_ms", "median_ms", "min_ms", "max_ms"))
    for variant in order:
        values = samples[variant]
        if len(values) != requested_runs:
            raise SystemExit(
                f"expected {requested_runs} build samples for {variant}, found {len(values)}"
            )
        writer.writerow((
            variant,
            len(values),
            f"{statistics.fmean(values):.6f}",
            f"{statistics.median(values):.6f}",
            f"{min(values):.6f}",
            f"{max(values):.6f}",
        ))
PY

if [[ ! -f "${search_runs_csv}" ]]; then
  printf 'layer,file,run,invocation,time_ms\n' > "${search_runs_csv}"
fi
if [[ ! -f "${elaboration_runs_csv}" ]]; then
  printf 'layer,file,run,wall_ms,ibubble_total_ms,invocations\n' > "${elaboration_runs_csv}"
fi

search_sample_valid() {
  python3 - "${search_runs_csv}" "${elaboration_runs_csv}" "$1" "$2" <<'PY'
import csv
import sys

raw_path, wall_path, file, run = sys.argv[1:]
with open(raw_path, newline="", encoding="utf-8") as stream:
    raw = [
        row for row in csv.DictReader(stream)
        if row["file"] == file and row["run"] == run
    ]
with open(wall_path, newline="", encoding="utf-8") as stream:
    wall = [
        row for row in csv.DictReader(stream)
        if row["file"] == file and row["run"] == run
    ]
if len(wall) != 1 or not raw:
    raise SystemExit(1)
wall_ms = float(wall[0]["wall_ms"])
values = [float(row["time_ms"]) for row in raw]
expected = int(wall[0]["invocations"])
valid = (
    len(values) == expected
    and sum(values) <= wall_ms * 1.05
    and max(values) <= wall_ms * 1.05
)
raise SystemExit(0 if valid else 1)
PY
}

remove_search_sample() {
  python3 - "${search_runs_csv}" "${elaboration_runs_csv}" "$1" "$2" <<'PY'
import csv
import pathlib
import sys

raw_path, wall_path, file, run = sys.argv[1:]
for name in (raw_path, wall_path):
    path = pathlib.Path(name)
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        fieldnames = reader.fieldnames
        rows = [
            row for row in reader
            if not (row["file"] == file and row["run"] == run)
        ]
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    temporary.replace(path)
PY
}

search_root="$(cd -- "${script_dir}/../IrisITreeBubble" && pwd)"
while IFS= read -r source; do
  relative="${source#${repo_root}/}"
  within_variant="${source#${search_root}/}"
  layer="${within_variant%%/*}"
  safe_name="${within_variant//\//_}"
  safe_name="${safe_name%.lean}"
  for run in $(seq 1 "${runs}"); do
    timing_log="${log_dir}/search-${safe_name}-run-${run}.log"
    if search_sample_valid "${relative}" "${run}"; then
      echo "[search cached ${run}/${runs}] ${relative}" >&2
      continue
    fi
    remove_search_sample "${relative}" "${run}"
    if [[ -f "${timing_log}" ]]; then
      mv "${timing_log}" "${timing_log%.log}-rejected-cached.log"
    fi
    attempt=1
    while true; do
      echo "[search ${run}/${runs}, attempt ${attempt}] ${relative}" >&2
      if ! wall_ms="$(python3 - "${timing_log}" "${source}" <<'PY'
import pathlib
import subprocess
import sys
import time

log = pathlib.Path(sys.argv[1])
source = sys.argv[2]
started = time.perf_counter()
with log.open("w", encoding="utf-8") as stream:
    completed = subprocess.run(
        ["lake", "env", "lean", "-DElab.async=false", "-Dibubble.timing=true", source],
        stdout=stream,
        stderr=subprocess.STDOUT,
        check=False,
    )
print(f"{(time.perf_counter() - started) * 1000:.6f}")
raise SystemExit(completed.returncode)
PY
)"; then
        echo "Lean failed for ${relative}; see ${timing_log}" >&2
        exit 1
      fi

      invocation_summary="$(awk '
        /IBUBBLE_CORE_TIME_NS/ {
          value = ($NF + 0) / 1000000
          count += 1
          total += value
          if (value > maximum) maximum = value
        }
        END { printf "%.6f,%d,%.6f", total, count, maximum }
      ' "${timing_log}")"
      IFS=, read -r invocation_total invocation_count invocation_max <<< "${invocation_summary}"
      if [[ "${invocation_count}" == "0" ]]; then
        echo "No ibubble timing markers found in ${relative}; see ${timing_log}" >&2
        exit 1
      fi
      if python3 - "${wall_ms}" "${invocation_total}" "${invocation_max}" <<'PY'
import sys

wall, total, maximum = map(float, sys.argv[1:])
raise SystemExit(0 if total <= wall * 1.05 and maximum <= wall * 1.05 else 1)
PY
      then
        break
      fi
      rejected_log="${timing_log%.log}-rejected-attempt-${attempt}.log"
      mv "${timing_log}" "${rejected_log}"
      echo "Discarded impossible internal timing (wall=${wall_ms}ms, total=${invocation_total}ms, max=${invocation_max}ms); see ${rejected_log}" >&2
      attempt=$((attempt + 1))
      if [[ "${attempt}" -gt 5 ]]; then
        echo "Could not obtain a consistent timing sample for ${relative} run ${run}" >&2
        exit 1
      fi
    done

    invocation_summary="${invocation_total},${invocation_count}"
    printf '%s,%s,%s,%s,%s\n' "${layer}" "${relative}" "${run}" "${wall_ms}" "${invocation_summary}" >> "${elaboration_runs_csv}"
    awk -v layer="${layer}" -v file="${relative}" -v run="${run}" '
      /IBUBBLE_CORE_TIME_NS/ {
        invocation += 1
        printf "%s,%s,%d,%d,%.6f\n", layer, file, run, invocation, ($NF + 0) / 1000000
      }
    ' "${timing_log}" >> "${search_runs_csv}"
  done
done < <(
  find "${search_root}/Core" "${search_root}/Effects" "${search_root}/HeapLang" -type f -name '*.lean' -print |
    LC_ALL=C sort |
    while IFS= read -r source; do
      if grep -Eq '^[[:space:]]*ibubble\??([[:space:]]|$)' "${source}"; then
        echo "${source}"
      fi
    done
)

python3 - "${search_runs_csv}" "${elaboration_runs_csv}" "${search_invocations_csv}" "${search_files_csv}" "${search_layers_csv}" "${runs}" <<'PY'
import collections
import csv
import statistics
import sys

raw_path, wall_path, invocation_path, file_path, layer_path, requested_runs = sys.argv[1:]
requested_runs = int(requested_runs)

def percentile(values, percent):
    ordered = sorted(values)
    position = (len(ordered) - 1) * percent / 100
    lower = int(position)
    upper = min(lower + 1, len(ordered) - 1)
    fraction = position - lower
    return ordered[lower] + (ordered[upper] - ordered[lower]) * fraction

with open(raw_path, newline="", encoding="utf-8") as stream:
    raw = [
        row for row in csv.DictReader(stream)
        if int(row["run"]) <= requested_runs
    ]
with open(wall_path, newline="", encoding="utf-8") as stream:
    wall = [
        row for row in csv.DictReader(stream)
        if int(row["run"]) <= requested_runs
    ]

calls_by_file_run = collections.Counter(
    (row["layer"], row["file"], int(row["run"])) for row in raw
)
calls_by_file = collections.defaultdict(set)
for (layer, file, _), count in calls_by_file_run.items():
    calls_by_file[(layer, file)].add(count)
inconsistent = {
    key: sorted(counts) for key, counts in calls_by_file.items() if len(counts) != 1
}
if inconsistent:
    raise SystemExit(f"inconsistent dynamic call counts between runs: {inconsistent}")
for key, counts in calls_by_file.items():
    samples = sum(
        1 for layer, file, _ in calls_by_file_run if (layer, file) == key
    )
    if samples != requested_runs:
        raise SystemExit(
            f"expected {requested_runs} search samples for {key}, found {samples}"
        )

by_invocation = collections.defaultdict(list)
for row in raw:
    by_invocation[(row["layer"], row["file"], int(row["invocation"]))].append(
        float(row["time_ms"])
    )
with open(invocation_path, "w", newline="", encoding="utf-8") as stream:
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow(("layer", "file", "invocation", "samples", "mean_ms", "min_ms", "max_ms"))
    for (layer, file, invocation), values in sorted(by_invocation.items()):
        writer.writerow((
            layer, file, invocation, len(values),
            f"{statistics.fmean(values):.6f}",
            f"{min(values):.6f}",
            f"{max(values):.6f}",
        ))

by_file_run_total = collections.defaultdict(float)
for row in raw:
    by_file_run_total[(row["layer"], row["file"], int(row["run"]))] += float(row["time_ms"])
by_file_wall = collections.defaultdict(list)
by_file_calls = {}
for row in wall:
    key = (row["layer"], row["file"])
    by_file_wall[key].append(float(row["wall_ms"]))
    by_file_calls[key] = int(row["invocations"])
with open(file_path, "w", newline="", encoding="utf-8") as stream:
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow((
        "layer", "file", "runs", "calls_per_run", "mean_search_total_ms",
        "mean_wall_ms", "median_wall_ms", "min_wall_ms", "max_wall_ms",
    ))
    for key in sorted(by_file_wall):
        layer, file = key
        wall_values = by_file_wall[key]
        search_totals = [
            value for (run_layer, run_file, _), value in by_file_run_total.items()
            if (run_layer, run_file) == key
        ]
        writer.writerow((
            layer, file, len(wall_values), by_file_calls[key],
            f"{statistics.fmean(search_totals):.6f}",
            f"{statistics.fmean(wall_values):.6f}",
            f"{statistics.median(wall_values):.6f}",
            f"{min(wall_values):.6f}",
            f"{max(wall_values):.6f}",
        ))

layer_order = ("Core", "Effects", "HeapLang")
with open(layer_path, "w", newline="", encoding="utf-8") as stream:
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow((
        "layer", "calls_per_run", "samples", "median_call_ms", "p90_call_ms",
        "p95_call_ms", "max_call_ms", "mean_total_ms",
    ))
    for layer in (*layer_order, "TOTAL"):
        selected = raw if layer == "TOTAL" else [row for row in raw if row["layer"] == layer]
        values = [float(row["time_ms"]) for row in selected]
        calls = len({(row["file"], int(row["invocation"])) for row in selected})
        per_run = collections.defaultdict(float)
        for row in selected:
            per_run[int(row["run"])] += float(row["time_ms"])
        writer.writerow((
            layer,
            calls,
            len(values),
            f"{statistics.median(values):.6f}",
            f"{percentile(values, 90):.6f}",
            f"{percentile(values, 95):.6f}",
            f"{max(values):.6f}",
            f"{statistics.fmean(per_run.values()):.6f}",
        ))
PY

python3 - "${tactic_csv}" "${build_summary_csv}" "${search_layers_csv}" "${search_files_csv}" "${runs}" "${report_md}" <<'PY'
import csv
import pathlib
import sys

tactic_path, build_path, search_path, search_files_path, runs, report_path = sys.argv[1:]

def read_csv(path):
    with open(path, newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))

tactics = read_csv(tactic_path)
builds = read_csv(build_path)
search = read_csv(search_path)
search_files = read_csv(search_files_path)
total_tactics = next(row for row in tactics if row["layer"] == "TOTAL")
lines = [
    "# IrisITree benchmark results",
    "",
    "## Proof size",
    "",
    "| Layer | Files | ibubble commands | Manual Iris | Search Iris | Reduction | Generated Iris | Manual all | Search all | Reduction | Generated all |",
    "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
]
for row in tactics:
    lines.append(
        f'| {row["layer"]} | {row["files"]} | {row["search_commands"]} | '
        f'{row["manual_iris"]} | {row["search_iris"]} | '
        f'{float(row["iris_reduction_percent"]):.1f}% | {row["generated_iris"]} | '
        f'{row["manual_all"]} | {row["search_all"]} | '
        f'{float(row["all_reduction_percent"]):.1f}% | {row["generated_all"]} |'
    )

lines.extend([
    "",
    "Iris counts Iris Proof Mode tactics, including each ibubble command. All adds "
    "ordinary Lean tactics. Reductions compare the handwritten manual variant "
    "with the search variant. Generated-script counts are reported separately "
    "because they measure persisted reconstruction code rather than handwritten "
    "proof reduction.",
    "",
    "## Complete case-study rebuild",
    "",
    "| Variant | Runs | Mean | Median | Min | Max |",
    "|---|---:|---:|---:|---:|---:|",
])
for row in builds:
    lines.append(
        f'| {row["variant"]} | {row["runs"]} | '
        f'{float(row["mean_ms"]) / 1000:.3f} s | '
        f'{float(row["median_ms"]) / 1000:.3f} s | '
        f'{float(row["min_ms"]) / 1000:.3f} s | '
        f'{float(row["max_ms"]) / 1000:.3f} s |'
    )

lines.extend([
    "",
    "Each sample deletes only the selected variant's Lean artifacts and "
    "rebuilds its aggregate module. Variant order rotates between repetitions.",
    "",
    "## Search cost per run",
    "",
    "| Layer | Calls/run | Samples | Median/call | P90/call | P95/call | Max/call | Mean cumulative search/run |",
    "|---|---:|---:|---:|---:|---:|---:|---:|",
])
for row in search:
    lines.append(
        f'| {row["layer"]} | {row["calls_per_run"]} | {row["samples"]} | '
        f'{float(row["median_call_ms"]) / 1000:.3f} s | '
        f'{float(row["p90_call_ms"]) / 1000:.3f} s | '
        f'{float(row["p95_call_ms"]) / 1000:.3f} s | '
        f'{float(row["max_call_ms"]) / 1000:.3f} s | '
        f'{float(row["mean_total_ms"]) / 1000:.3f} s |'
    )

lines.extend([
    "",
    f'Calls/run counts dynamic Search.search calls; Samples covers all '
    f'repetitions. The {total_tactics["search_commands"]} textual ibubble '
    f'commands expand to {next(row for row in search if row["layer"] == "TOTAL")["calls_per_run"]} '
    "calls per run because goal combinators may invoke a command for multiple "
    "goals. P90/call and P95/call summarize the pooled per-call samples.",
    "",
    "Mean cumulative search/run sums calls measured with Elab.async=false; "
    "complete rebuild reports parallel wall-clock time, so these totals are "
    "not directly comparable.",
    "",
])
pathlib.Path(report_path).write_text("\n".join(lines), encoding="utf-8")
PY

echo "Wrote ${report_md}"
echo "Wrote ${tactic_csv}"
echo "Wrote ${build_summary_csv}"
echo "Wrote ${search_layers_csv}"
echo "Raw samples are under ${output_dir}"
