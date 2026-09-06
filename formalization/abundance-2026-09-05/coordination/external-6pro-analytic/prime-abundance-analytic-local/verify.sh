#!/usr/bin/env bash
# Fresh, pinned source execution. A setup check or partial build is not success.
# Usage: bash verify.sh [existing-pinned-Lake-workspace]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
WORKSPACE="${1:-$ROOT}"
WORKSPACE="$(cd "$WORKSPACE" && pwd)"
EXPECTED_MATHLIB=a3a10db0e9d66acbebf76c5e6a135066525ac900
mkdir -p "$ROOT/logs"
LOGS="$(mktemp -d "$ROOT/logs/lean-run-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX")"
python3 "$ROOT/static_audit.py" --json "$LOGS/source-audit.json"
python3 - "$LOGS/source-audit.json" > "$LOGS/compile-order.txt" <<'PY'
import json, sys
print('\n'.join(json.load(open(sys.argv[1]))['compile_order']))
PY
if ! command -v lake >/dev/null 2>&1; then
  echo 'STOP: lake is not installed; no Lean elaboration attempted.' >&2
  exit 127
fi
cd "$WORKSPACE"
lake env lean --version | tee "$LOGS/lean-version.txt"
python3 "$ROOT/verification_guards.py" version "$LOGS/lean-version.txt"
MATHLIB="$WORKSPACE/.lake/packages/mathlib"
[[ -d "$MATHLIB" ]] || {
  echo 'STOP: mathlib dependency absent; initialize the pinned workspace first.' >&2; exit 2;
}
REV="$(git -C "$MATHLIB" rev-parse HEAD)"
printf '%s\n' "$REV" > "$LOGS/mathlib-revision.txt"
[[ "$REV" == "$EXPECTED_MATHLIB" ]] || {
  echo 'STOP: wrong mathlib revision.' >&2; exit 2;
}
[[ -z "$(git -C "$MATHLIB" status --porcelain --untracked-files=no)" ]] || {
  echo 'STOP: tracked mathlib source files are modified.' >&2; exit 2;
}
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
OUT="$TMP/objects"
STAGE="$TMP/sources"
mkdir -p "$OUT" "$STAGE"
python3 "$ROOT/verification_guards.py" snapshot "$ROOT" "$STAGE" \
  "$LOGS/source-audit.json" "$LOGS/execution-support.json"
run_lean() {
  # Invoked from WORKSPACE so relative Lake search paths can be normalized before cd.
  lake env python3 "$ROOT/verification_guards.py" run-lean "$STAGE" "$OUT" -- "$@"
}
# Compile only the staged, audited source into new objects. No local cached objects
# are copied to either temporary tree. Upstream mathlib's cache remains permitted.
while IFS= read -r module; do
  relative="${module//./\/}"
  mkdir -p "$OUT/$(dirname "$relative")"
  printf '\n=== %s ===\n' "$module"
  run_lean -o "$OUT/$relative.olean" "$STAGE/$relative.lean" \
    2>&1 | tee "$LOGS/$module.log"
  [[ -s "$OUT/$relative.olean" ]] || {
    echo "STOP: no fresh object emitted for $module." >&2; exit 2;
  }
done < "$LOGS/compile-order.txt"
python3 "$ROOT/check_axioms.py" "$LOGS/GoalCheck.log" --json "$LOGS/axioms.json"
python3 "$ROOT/static_audit.py" --json "$LOGS/source-audit-after.json"
python3 "$ROOT/verification_guards.py" unchanged "$ROOT" "$LOGS/execution-support.json"
python3 - "$LOGS" <<'PY'
from pathlib import Path
import json, sys
root = Path(sys.argv[1])
before = json.loads((root/'source-audit.json').read_text())
after = json.loads((root/'source-audit-after.json').read_text())
if before['files'] != after['files']:
    raise SystemExit('STOP: source files changed during compilation')
report = {
    'status':'FINAL_GOAL_ELABORATED_AND_REQUIRED_AXIOM_REPORTS_ACCEPTED',
    'lean_version':(root/'lean-version.txt').read_text().strip(),
    'mathlib_commit':(root/'mathlib-revision.txt').read_text().strip(),
    'target':'PrimeAbundance.prime_abundance : PrimeAbundance.PrimeAbundanceClaim',
    'target_sha256':before['target_sha256'],
    'goalcheck_sha256':before['goalcheck_sha256'],
    'source_files':before['files'],
    'execution_support':json.loads((root/'execution-support.json').read_text()),
    'axioms':json.loads((root/'axioms.json').read_text()),
    'scope':'The locked prime-abundance claim; not ESC and not a full-mathlib source rebuild.'
}
(root/'verification-result.json').write_text(json.dumps(report,indent=2)+'\n')
print('Final declaration, locked target, fresh local source builds, and axiom reports passed.')
PY
printf 'Logs: %s\n' "$LOGS"
