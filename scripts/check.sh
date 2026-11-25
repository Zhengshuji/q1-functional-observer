#!/usr/bin/env bash
# Build the Paper I Lean project and audit its axioms -- the local equivalent of the `lean` CI job.
#
# Kept in step with .github/workflows/build.yml.  If a step is added there, add it here too.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

# 1. the mathematics compiles
lake build Q1Paper.PaperI.MainTheorems
lake env lean PaperI.lean
lake build Q1Paper.PaperI.Read.All

# 2. the axiom audit
lake env lean Q1Paper/PaperI/Audit.lean > "${TMPDIR:-/tmp}/paperI_audit.log"
python3 scripts/check_paperI_axioms.py "${TMPDIR:-/tmp}/paperI_audit.log" Q1Paper/PaperI/Audit.lean

# 3. the generated indexes must match the sources
python3 scripts/generate_paperI_claims.py --check
python3 scripts/generate_paperI_modules.py --check
python3 scripts/paper_lean_index.py --check
python3 scripts/generate_reading_entries.py --check
python3 scripts/check_consistency.py

echo "all checks passed"
