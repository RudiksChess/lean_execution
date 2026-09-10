"""Enforce the axiom policy on fresh Lean output, independently of certificates."""

import re
import subprocess
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDITS = {
    "Thesis/Prop/Audit.lean": {
        "Thesis.Prop." + name
        for name in ("completeness_ND", "soundComplete", "soundness", "ex_id", "ex_dne")
    },
    "Thesis/Sort/Audit.lean": {
        "Thesis.Sort." + name
        for name in ("quicksort_correct", "quicksort_perm", "quicksort_sorted")
    },
}
LINE = re.compile(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
)


def validate(output, expected):
    """Reject forbidden axioms, missing targets, duplicates and unexpected output."""
    seen = set()
    for line in output.splitlines():
        if not line.strip():
            continue
        match = LINE.fullmatch(line)
        if match is None:
            raise ValueError(f"Unexpected audit output: {line}")
        name, raw = match.groups()
        if name not in expected or name in seen:
            raise ValueError(f"Unexpected or duplicate theorem: {name}")
        seen.add(name)
        axioms = {item.strip() for item in raw.split(",")} if raw else set()
        forbidden = axioms - ALLOWED
        if forbidden:
            raise ValueError(f"{name}: forbidden axioms {sorted(forbidden)}")
    if seen != expected:
        raise ValueError(f"Missing audited theorems: {sorted(expected - seen)}")


def main():
    root = Path(__file__).resolve().parents[1]
    for source, expected in AUDITS.items():
        result = subprocess.run(
            ["lake", "env", "lean", source], cwd=root,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
        )
        if result.stderr.strip():
            raise ValueError(f"Unexpected diagnostics for {source}: {result.stderr}")
        validate(result.stdout, expected)
        print(f"Axiom policy passed: {source} ({len(expected)} theorems)")


if __name__ == "__main__":
    main()
