#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/../.." && pwd)"
runs="${1:-5}"
output_dir="${script_dir}/timing"
raw_csv="${output_dir}/ibubble_runs.csv"
invocation_csv="${output_dir}/ibubble_invocations.csv"
file_csv="${output_dir}/ibubble_files.csv"
report_md="${output_dir}/README.md"

if ! [[ "${runs}" =~ ^[1-9][0-9]*$ ]]; then
  echo "usage: $0 [positive-number-of-runs]" >&2
  exit 2
fi

mkdir -p "${output_dir}"
printf 'file,run,invocation,time_ms\n' > "${raw_csv}"

cd "${repo_root}"
while IFS= read -r source; do
  relative="${source#${repo_root}/}"
  for run in $(seq 1 "${runs}"); do
    timing_log="$(mktemp -t bubble-irisitree-timing)"
    echo "[${run}/${runs}] ${relative}" >&2
    if ! lake env lean \
        -DElab.async=false \
        -Dibubble.timing=true \
        "${source}" >"${timing_log}" 2>&1; then
      failure_log="${output_dir}/$(basename "${source}" .lean)-run-${run}.log"
      mv "${timing_log}" "${failure_log}"
      echo "Lean failed for ${relative}; see ${failure_log}" >&2
      exit 1
    fi
    awk -v file="${relative}" -v run="${run}" '
      /IBUBBLE_CORE_TIME_NS/ {
        invocation += 1
        printf "%s,%d,%d,%.6f\n", file, run, invocation, ($NF + 0) / 1000000
      }
    ' "${timing_log}" >> "${raw_csv}"
    rm -f "${timing_log}"
  done
done < <(find "${script_dir}" -type f -name '*.lean' | LC_ALL=C sort)

printf 'file,invocation,samples,average_ms,min_ms,max_ms\n' > "${invocation_csv}"
awk -F, 'NR > 1 {
  key = $1 SUBSEP $3
  file[key] = $1
  invocation[key] = $3
  count[key] += 1
  sum[key] += $4
  if (!(key in min) || $4 < min[key]) min[key] = $4
  if (!(key in max) || $4 > max[key]) max[key] = $4
}
END {
  for (key in count)
    printf "%s,%d,%d,%.6f,%.6f,%.6f\n",
      file[key], invocation[key], count[key], sum[key] / count[key], min[key], max[key]
}' "${raw_csv}" | LC_ALL=C sort -t, -k1,1 -k2,2n >> "${invocation_csv}"

printf 'file,runs,invocations_per_run,average_total_ms,min_total_ms,max_total_ms\n' > "${file_csv}"
awk -F, 'NR > 1 {
  runKey = $1 SUBSEP $2
  runFile[runKey] = $1
  runTotal[runKey] += $4
  runCalls[runKey] += 1
}
END {
  for (runKey in runTotal) {
    f = runFile[runKey]
    fileRuns[f] += 1
    fileTotal[f] += runTotal[runKey]
    if (!(f in min) || runTotal[runKey] < min[f]) min[f] = runTotal[runKey]
    if (!(f in max) || runTotal[runKey] > max[f]) max[f] = runTotal[runKey]
    if (runCalls[runKey] > calls[f]) calls[f] = runCalls[runKey]
  }
  for (f in fileRuns)
    printf "%s,%d,%d,%.6f,%.6f,%.6f\n",
      f, fileRuns[f], calls[f], fileTotal[f] / fileRuns[f], min[f], max[f]
}' "${raw_csv}" | LC_ALL=C sort -t, -k1,1 >> "${file_csv}"

{
  echo '# IrisITree `ibubble` timings'
  echo
  echo "Each source file was elaborated ${runs} times with \`Elab.async=false\`."
  echo 'Times measure `Search.search`, including proof replay, and are summed per file.'
  echo
  echo '| File | Invocations/run | Average total (ms) | Min (ms) | Max (ms) |'
  echo '|---|---:|---:|---:|---:|'
  tail -n +2 "${file_csv}" | while IFS=, read -r file run_count calls average minimum maximum; do
    printf '| `%s` | %s | %.3f | %.3f | %.3f |\n' \
      "${file}" "${calls}" "${average}" "${minimum}" "${maximum}"
  done
  echo
  echo 'Per-invocation measurements are in `ibubble_invocations.csv`; raw runs are in `ibubble_runs.csv`.'
  echo
  echo 'The arithmetic mean can be sensitive to large search-time outliers; retain the raw samples with any reported mean.'
  echo
  echo '## Generated proof comparison'
  echo
  echo 'The generated explicit `wpi_fork` comparison is recorded in `WpiForkGenerated.lean`.'
  echo 'Its five synchronous theorem-elaboration measurements were 53, 53, 53, 53, and 54 ms (53.2 ms average).'
} > "${report_md}"

echo "Wrote ${report_md}"
echo "Wrote ${file_csv}"
echo "Wrote ${invocation_csv}"
echo "Wrote ${raw_csv}"
