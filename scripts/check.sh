#!/usr/bin/env bash
# Build the paper Lean project and audit axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
lake build Q1Paper
lake env lean Q1Paper/Audit.lean
