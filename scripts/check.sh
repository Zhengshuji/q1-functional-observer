#!/usr/bin/env bash
# Build the Paper I Lean project and audit its axioms -- the local equivalent of the `lean` CI job.
#
# Kept in step with .github/workflows/build.yml.  If a step is added there, add it here too.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

# 1. the mathematics compiles
lake build Q1Paper.PaperI.S00_Interface.MainTheorems
lake env lean PaperI.lean
lake build Q1Paper.PaperI.Read.All

# 2. the axiom audit
lake env lean Q1Paper/PaperI/S00_Interface/Audit.lean > "${TMPDIR:-/tmp}/paperI_audit.log"
python3 scripts/check_paperI_axioms.py "${TMPDIR:-/tmp}/paperI_audit.log" Q1Paper/PaperI/S00_Interface/Audit.lean

# 2b. Paper II
lake build Q1Paper.PaperII.MainTheorems
lake env lean Q1Paper/PaperII/ClaimsCheck.lean
lake build Q1Paper.PaperII.Read.All
lake env lean Q1Paper/PaperII/Audit.lean > "${TMPDIR:-/tmp}/paperII_audit.log"
python3 scripts/check_paperI_axioms.py "${TMPDIR:-/tmp}/paperII_audit.log" Q1Paper/PaperII/Audit.lean

# 2c. Paper V
lake build Q1Paper.PaperV.MainTheorems
lake env lean Q1Paper/PaperV/ClaimsCheck.lean
lake build Q1Paper.PaperV.Read.All
lake env lean Q1Paper/PaperV/Audit.lean > "${TMPDIR:-/tmp}/paperV_audit.log"
python3 scripts/check_paperI_axioms.py "${TMPDIR:-/tmp}/paperV_audit.log" Q1Paper/PaperV/Audit.lean
python3 scripts/check_paperV_counts.py
lake env lean Q1Paper/PaperV/ThinCounterexample.lean > "${TMPDIR:-/tmp}/paperV_thin.log"

# 3. the generated indexes must match the sources
python3 scripts/generate_paperI_claims.py --check
python3 scripts/generate_paperI_modules.py --check
python3 scripts/generate_paperII_modules.py --check
python3 scripts/generate_paperII_claims.py --check
python3 scripts/generate_audit.py --check
python3 scripts/paper_lean_index.py --check
python3 scripts/generate_reading_entries.py --check
python3 scripts/check_consistency.py
python3 scripts/check_pdf_fresh.py
python3 scripts/check_audit_coverage.py

echo "all checks passed"
