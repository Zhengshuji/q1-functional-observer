#!/usr/bin/env python3
"""Tag the historical documents in `docs/` so they cannot be mistaken for current status.

Several files under `docs/` record a stage of the work: reviews, retractions, audits and roadmaps.
They are worth keeping -- they say what was believed and why it changed -- but a reader who opens one
of them without context will read closed gaps as open ones.  This script inserts a two-line banner
after the title of each historical file, pointing at the current entry point.

It is idempotent: a file that already carries the banner is left alone.

Usage:
    python scripts/tag_historical_docs.py --dry-run
    python scripts/tag_historical_docs.py
"""

from __future__ import annotations

import argparse
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"

BANNER_START = "> **Historical record.**"
BANNER = (
    "> **Historical record.** This file documents a stage of the work and is kept for provenance.\n"
    "> Gaps it describes may have been closed since; do not read it as the current status.\n"
    "> Current status and the reading entry point: [START_HERE.md](START_HERE.md).\n"
)

HISTORICAL = [
    "ALGORITHM_REVIEW.md",
    "LEAN_MAP.md",
    "PAPER_I_CLAIM19_CRAMER.md",
    "PAPER_I_FORMALIZATION_MAP.md",
    "PAPER_I_MASTER_ROADMAP.md",
    "PAPER_I_MATH_AUDIT.md",
    "PAPER_I_REUSE_AUDIT.md",
    "REPLY_from_paper_agent.md",
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    changed, skipped, missing = [], [], []
    for name in HISTORICAL:
        path = DOCS / name
        if not path.exists():
            missing.append(name)
            continue
        text = path.read_text(encoding="utf-8")
        if BANNER_START in text:
            skipped.append(name)
            continue
        lines = text.splitlines(keepends=True)
        # insert after the first heading line, so the title stays first
        at = 0
        for i, line in enumerate(lines):
            if line.startswith("#"):
                at = i + 1
                break
        new = "".join(lines[:at]) + "\n" + BANNER + "\n" + "".join(lines[at:])
        changed.append(name)
        if not args.dry_run:
            path.write_text(new, encoding="utf-8", newline="\n")

    verb = "would tag" if args.dry_run else "tagged"
    print(f"{verb} {len(changed)} historical documents; {len(skipped)} already tagged; {len(missing)} missing")
    for name in changed:
        print(f"  {name}")
    for name in missing:
        print(f"  MISSING: {name}")
    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
