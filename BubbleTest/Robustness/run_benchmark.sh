#!/usr/bin/env bash
set -eu
export PYTHONDONTWRITEBYTECODE=1

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
python_bin="${BUBBLE_PYTHON:-python3}"
plot_python_bin="${BUBBLE_PLOT_PYTHON:-${python_bin}}"
output_dir="${script_dir}/result"
expect_output_dir=false

for argument in "$@"; do
  if [[ "${argument}" == "-h" || "${argument}" == "--help" ]]; then
    exec "${python_bin}" "${script_dir}/sweep.py" "$@"
  fi
  if [[ "${expect_output_dir}" == true ]]; then
    output_dir="${argument}"
    expect_output_dir=false
    continue
  fi
  case "${argument}" in
    --out)
      expect_output_dir=true
      ;;
    --out=*)
      output_dir="${argument#--out=}"
      ;;
  esac
done

if ! "${plot_python_bin}" -c 'import matplotlib, numpy' >/dev/null 2>&1; then
  echo "PNG output requires matplotlib and numpy; no experiments were started." >&2
  echo "Install them with: ${plot_python_bin} -m pip install matplotlib numpy" >&2
  echo "Or set BUBBLE_PLOT_PYTHON to a Python that already has them." >&2
  exit 1
fi

"${python_bin}" "${script_dir}/sweep.py" "$@"
"${plot_python_bin}" "${script_dir}/plot.py" "${output_dir}" \
  --min-seeds 1 --out "${output_dir}/architecture_comparison.png"
