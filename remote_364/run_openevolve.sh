#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
. .venv/bin/activate
: "${OPENAI_API_KEY:?set OPENAI_API_KEY for HKGAI-compatible endpoint}"
: "${OPENAI_BASE_URL:?set OPENAI_BASE_URL for HKGAI-compatible endpoint, e.g. https://.../v1}"
: "${OPENAI_MODEL:=t2_qwen3-5-122b-a10b_fp8_262k}"
python3 - <<'PY'
import os, pathlib
base = os.environ['OPENAI_BASE_URL']
key = os.environ['OPENAI_API_KEY']
model = os.environ.get('OPENAI_MODEL', 't2_qwen3-5-122b-a10b_fp8_262k')
out = pathlib.Path('.openevolve_runtime.yaml')
out.write_text(f'''max_iterations: 20
checkpoint_interval: 5
log_level: INFO
diff_based_evolution: true
llm:
  api_base: {base}
  api_key: {key}
  models:
    - name: {model}
      weight: 1.0
  temperature: 0.4
  max_tokens: 2048
evaluator:
  timeout: 120
  parallel_evaluations: 1
database:
  population_size: 20
  archive_size: 20
  num_islands: 2
''')
out.chmod(0o600)
PY
openevolve-run openevolve_initial.py openevolve_evaluator.py \
  --config .openevolve_runtime.yaml \
  --iterations "${1:-20}" \
  --output openevolve_output
