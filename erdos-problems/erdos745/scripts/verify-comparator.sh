#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
local_check=false
if [[ $# -eq 1 && ${1:-} == --local ]]; then
  local_check=true
elif [[ $# -ne 0 ]]; then
  echo 'usage: scripts/verify-comparator.sh [--local]' >&2
  exit 2
fi
if [[ $local_check == false ]] && ! command -v bwrap >/dev/null 2>&1; then
  echo 'The protected check requires Linux and bubblewrap; --local runs an unsandboxed audit.' >&2
  exit 2
fi
prefix=$(lean --print-prefix)
for tool in leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool"
done
config=$(mktemp "${TMPDIR:-/tmp}/erdos745-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import sys
from pathlib import Path
source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text())
if 'external_kernels' in config:
    raise SystemExit('external_kernels must not appear in the submission config')
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [f'{prefix}/bin/nanoda_bin'],
    'con-ron': [f'{prefix}/bin/con-ron'],
}
Path(destination).write_text(json.dumps(config, indent=2) + '\n')
PY
if [[ $local_check == true ]]; then
  lake comparator --config "$config" --inadvisably-no-sandbox
else
  lake comparator --config "$config"
fi
