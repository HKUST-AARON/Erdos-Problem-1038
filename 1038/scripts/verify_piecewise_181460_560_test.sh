#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

CERT_JSON="piecewise_five_atom_181460_560blocks_margin_tuned_candidate.json"
OUT="certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.json"

python3 verify_piecewise_tail_correct_domain.py "$CERT_JSON" --gap-scan
python3 scripts/generate_piecewise_560_181460_certificate.py > "$OUT"
python3 - <<'PY'
import json
import sys
path = 'certificates/piecewise_five_atom_181460_560blocks_required_domain_certificate.json'
with open(path) as f:
    cert = json.load(f)
if cert.get('result') != 'PASS' or not cert.get('all_required_blocks_ok', False):
    print(f"[FAIL] {path}")
    sys.exit(1)
print(f"[OK] required-domain certificate pass for M={cert['M']}, K={cert['K']}")
print(f"[OK] required worst margin = {cert['overall_worst_required']['value']}")
print(f"[INFO] irrelevant-gap worst = {cert['irrelevant_gap_worst']['value']} (not required)")
PY
