#!/usr/bin/env python3
"""Generate the deterministic proof-explorer artifact from Lean elaborator states."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Any
from spanish_migration import CONFIG as SPANISH_CONFIG, translate


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "artifacts/explorer/proofs.json"
SOURCE_COMMIT = "6eecf5afeba4af39280bd98d2667f295baa94973"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.29.0"
LEAN_VERSION = "4.29.0"
SUBVERSO_REVISION = "52b9dfbd2658408e37ae6e8b72601ddeaaa25a0c"
LEGACY_STEPS: dict[str, list[dict[str, Any]]] = {}

ALLOWED_TACTICS = {
    "Lean.Parser.Tactic.intro",
    "Lean.Parser.Tactic.tacticHave__",
    "Lean.Parser.Tactic.exact",
    "Lean.Parser.Tactic.simpa",
    "Lean.Parser.Tactic.tacticLet__",
    "Lean.Parser.Tactic.rwSeq",
    "Lean.Parser.Tactic.change",
    "Lean.calcTactic",
}

# IDs are semantic and deliberately independent of line numbers. Lines below are
# fail-closed assertions against the source pinned by SOURCE_COMMIT.
EXPECTED: dict[str, list[tuple[str, str, int]]] = {
    "weakening": [
        ("weakening.hyp.intro", "weakening.hyp", 56),
        ("weakening.hyp.membership", "weakening.hyp", 57),
        ("weakening.hyp.close", "weakening.hyp", 58),
        ("weakening.impI.intro", "weakening.impI", 60),
        ("weakening.impI.extend-context", "weakening.impI", 61),
        ("weakening.impI.induction", "weakening.impI", 62),
        ("weakening.impI.close", "weakening.impI", 64),
        ("weakening.impE.intro", "weakening.impE", 66),
        ("weakening.impE.implication", "weakening.impE", 67),
        ("weakening.impE.argument", "weakening.impE", 68),
        ("weakening.impE.close", "weakening.impE", 69),
        ("weakening.negI.intro", "weakening.negI", 71),
        ("weakening.negI.extend-context", "weakening.negI", 72),
        ("weakening.negI.induction", "weakening.negI", 73),
        ("weakening.negI.close", "weakening.negI", 74),
        ("weakening.negE.intro", "weakening.negE", 76),
        ("weakening.negE.negative", "weakening.negE", 77),
        ("weakening.negE.positive", "weakening.negE", 78),
        ("weakening.negE.close", "weakening.negE", 79),
        ("weakening.botE.intro", "weakening.botE", 81),
        ("weakening.botE.induction", "weakening.botE", 82),
        ("weakening.botE.close", "weakening.botE", 83),
        ("weakening.classical.intro", "weakening.classical", 85),
        ("weakening.classical.extend-context", "weakening.classical", 86),
        ("weakening.classical.induction", "weakening.classical", 87),
        ("weakening.classical.close", "weakening.classical", 89),
    ],
    "quicksort_perm": [
        ("quicksort_perm.nil.close", "quicksort_perm.nil", 198),
        ("quicksort_perm.cons.small", "quicksort_perm.cons", 202),
        ("quicksort_perm.cons.large", "quicksort_perm.cons", 203),
        ("quicksort_perm.cons.small-decrease", "quicksort_perm.cons", 204),
        ("quicksort_perm.cons.large-decrease", "quicksort_perm.cons", 206),
        ("quicksort_perm.cons.recurse-small", "quicksort_perm.cons", 209),
        ("quicksort_perm.cons.recurse-large", "quicksort_perm.cons", 210),
        ("quicksort_perm.cons.partition", "quicksort_perm.cons", 211),
        ("quicksort_perm.cons.right", "quicksort_perm.cons", 214),
        ("quicksort_perm.cons.append", "quicksort_perm.cons", 216),
        ("quicksort_perm.cons.pivot", "quicksort_perm.cons", 219),
        ("quicksort_perm.cons.partition-cons", "quicksort_perm.cons", 222),
        ("quicksort_perm.cons.unfold", "quicksort_perm.cons", 224),
        ("quicksort_perm.cons.normalize-goal", "quicksort_perm.cons", 225),
        ("quicksort_perm.cons.close", "quicksort_perm.cons", 226),
        ("quicksort_perm.decrease-small.close", "quicksort_perm.decrease-small", 233),
        ("quicksort_perm.decrease-large.close", "quicksort_perm.decrease-large", 234),
    ],
}

TARGETS = [
    {
        "id": "weakening",
        "module": "Thesis.Prop.NaturalDeduction",
        "declaration": "Thesis.Prop.weakening",
        "shortDeclaration": "weakening",
        "path": "Thesis/Prop/NaturalDeduction.lean",
    },
    {
        "id": "quicksort_perm",
        "module": "Thesis.Sort.Quicksort",
        "declaration": "Thesis.Sort.quicksort_perm",
        "shortDeclaration": "quicksort_perm",
        "path": "Thesis/Sort/Quicksort.lean",
    },
]

# All remaining results in the two practical chapters, including the two parts
# of Lemma 11.19 and the helper/definition obligations of Proposition 12.6.
for module, declarations in [
    ("Thesis.Prop.NaturalDeduction", ["eval_Bot", "dni", "byCases", "sat_insert", "soundness", "isTautology_of_provable", "not_provable_Bot"]),
    ("Thesis.Prop.Completeness", ["lit_mem", "kalmar", "lit_congr", "litCtx_congr", "discharge", "completeness_ND", "soundComplete"]),
    ("Thesis.Prop.BridgeLemma", ["eval_tr"]),
    ("Thesis.Prop.CompletenessViaFoundation", ["provable_tr_of_tautology"]),
    ("Thesis.Sort.Quicksort", ["filter_length_le", "filter_length_lt_cons", "quicksort", "filter_partition_perm", "mem_quicksort", "pairwise_cons_iff", "pairwise_append_iff", "quicksort_sorted", "quicksort_correct"]),
]:
    for declaration in declarations:
        TARGETS.append({"id": declaration, "module": module,
                        "declaration": module.rsplit(".", 1)[0] + "." + declaration,
                        "shortDeclaration": declaration, "path": module.replace(".", "/") + ".lean"})


# Los identificadores públicos de navegación no se traducen. La declaración
# y todos sus estados proceden del módulo original con nombres españoles.
for target in TARGETS:
    target['shortDeclaration'] = SPANISH_CONFIG['public'].get(target['shortDeclaration'], target['shortDeclaration'])
    target['declaration'] = target['declaration'].rsplit('.', 1)[0] + '.' + target['shortDeclaration']


class ExportError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(args: list[str], *, text: bool = False) -> subprocess.CompletedProcess[Any]:
    return subprocess.run(
        args,
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=text,
    )


def assert_pins() -> None:
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != LEAN_TOOLCHAIN:
        raise ExportError(f"unexpected Lean toolchain: {toolchain!r}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    revisions = [
        package["rev"]
        for package in manifest["packages"]
        if package["name"] == "subverso"
    ]
    if revisions != [SUBVERSO_REVISION]:
        raise ExportError(f"unexpected SubVerso manifest pin: {revisions!r}")


def assert_source_unchanged(path: str) -> bytes:
    current = (ROOT / path).read_bytes()
    committed = run(["git", "show", f"{SOURCE_COMMIT}:{path}"]).stdout
    if current != committed:
        raise ExportError(
            f"{path} differs from source commit {SOURCE_COMMIT}; refusing stale export"
        )
    return current


def raw_export(module: str, declaration: str) -> dict[str, Any]:
    completed = run(
        ["lake", "exe", "proofExplorerExport", module, declaration], text=True
    )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise ExportError(
            f"Lean adapter emitted invalid JSON for {module}: {exc}"
        ) from exc


def normalized_steps(proof_id: str, raw: dict[str, Any]) -> list[dict[str, Any]]:
    if proof_id not in EXPECTED:
        return general_steps(proof_id, raw)
    tactics = [
        tactic
        for tactic in raw["proof"]["tactics"]
        if tactic["syntaxKind"] in ALLOWED_TACTICS
    ]
    expected = EXPECTED[proof_id]
    if len(tactics) != len(expected):
        raise ExportError(
            f"{proof_id}: expected {len(expected)} leaf tactics, got {len(tactics)}"
        )

    steps: list[dict[str, Any]] = []
    branch_seen: set[str] = set()
    for tactic, (step_id, branch, expected_line) in zip(tactics, expected):
        start = tactic["range"]["start"]
        end = tactic["range"]["end"]
        if start["line"] != expected_line:
            raise ExportError(
                f"{step_id}: expected source line {expected_line}, got {start['line']}"
            )
        if not tactic["before"]:
            raise ExportError(f"{step_id}: missing elaborator state before tactic")
        closes = not tactic["after"]
        expected_closure = step_id.endswith(".close")
        if closes != expected_closure:
            raise ExportError(
                f"{step_id}: expected "
                f"{'branch closure' if expected_closure else 'a following proof state'}"
            )
        if branch not in branch_seen and not closes:
            kind = "case"
        elif closes:
            kind = "closure"
        else:
            kind = "continuation"
        branch_seen.add(branch)

        # SubVerso preserves Lean's optional user-facing goal name. Recursive
        # equations often have anonymous metavariables, so give only those a
        # deterministic presentation ID; this does not alter goal contents.
        for phase in ("before", "after"):
            for index, goal in enumerate(tactic[phase], start=1):
                goal.setdefault("id", f"{step_id}.{phase}.goal-{index}")
        steps.append(
            {
                "id": step_id,
                "branch": branch,
                "label": tactic["sourceText"].splitlines()[0],
                "startLine": start["line"],
                "endLine": end["line"],
                "before": tactic["before"],
                "after": tactic["after"],
                "kind": kind,
                "sourceText": tactic["sourceText"],
            }
        )
    return steps


def general_steps(proof_id: str, raw: dict[str, Any]) -> list[dict[str, Any]]:
    """Leaf source tactics only, never wrapper snapshots that run whole subproofs.

    All goal text is supplied by Lean. IDs hash source text, not line positions;
    repeated identical tactics receive a stable occurrence suffix. Nested proof
    blocks retain Lean's goal names; their local closure is not global closure.
    """
    candidates = []
    for tactic in raw["proof"]["tactics"]:
        kind = tactic["syntaxKind"]
        if not (kind.startswith("Lean.Parser.Tactic.") or kind in {
            "Batteries.Tactic.byContra", "«tacticBy_cases_:_»", "Lean.calcTactic"
        }) or "tacticSeq" in kind:
            continue
        if not tactic["before"]:
            continue
        candidates.append(tactic)
    # SubVerso can record both a macro and its expansion at the same range.
    unique = {}
    for tactic in candidates:
        r = tactic["range"]
        key = (r["startByte"], r["endByte"])
        unique.setdefault(key, tactic)
    leaves = [(span, tactic) for span, tactic in unique.items()
              if not any(span[0] <= other[0] and other[1] <= span[1] and other != span
                         for other in unique)]
    leaves.sort(key=lambda item: item[0])
    if not leaves:
        raise ExportError(f"{proof_id}: no real source tactic states")
    counts: dict[str, int] = {}
    result = []
    for _, tactic in leaves:
        digest = sha256(tactic["sourceText"].encode())[:12]
        counts[digest] = counts.get(digest, 0) + 1
        step_id = f"{proof_id}.{digest}.{counts[digest]}"
        # Conserva enlaces compartidos solo si el mismo paso difiere exactamente
        # por el renombrado autorizado. No reutiliza estados de la versión antigua.
        matches = [old for old in LEGACY_STEPS.get(proof_id, [])
                   if old['startLine'] == tactic['range']['start']['line']
                   and old['endLine'] == tactic['range']['end']['line']
                   and translate(old['sourceText']) == tactic['sourceText']]
        if len(matches) == 1:
            step_id = matches[0]['id']
        goal_name = tactic["before"][0].get("id", "principal")
        for phase in ("before", "after"):
            for index, goal in enumerate(tactic[phase], 1):
                goal.setdefault("id", f"{step_id}.{phase}.goal-{index}")
        result.append({"id": step_id, "branch": f"{proof_id}.{goal_name}",
                       "label": tactic["sourceText"].splitlines()[0],
                       "startLine": tactic["range"]["start"]["line"],
                       "endLine": tactic["range"]["end"]["line"],
                       "before": tactic["before"], "after": tactic["after"],
                       "kind": "closure" if not tactic["after"] else "continuation",
                       "sourceText": tactic["sourceText"]})
    return result


def make_proof(target: dict[str, str]) -> dict[str, Any]:
    source_bytes = assert_source_unchanged(target["path"])
    raw = raw_export(target["module"], target["shortDeclaration"])
    proof = raw["proof"]
    if proof["declaration"] != target["shortDeclaration"]:
        raise ExportError(f"adapter returned wrong declaration for {target['id']}")
    declaration_range = proof["declarationRange"]
    code = proof["code"]
    steps = normalized_steps(target["id"], raw)
    blocks = []
    seen = set()
    for tactic in raw['proof']['tactics']:
        kind = tactic['syntaxKind']
        if not kind.startswith('Lean.Parser.Tactic.') or 'tacticSeq' in kind:
            continue
        start, end = tactic['range']['start']['line'], tactic['range']['end']['line']
        if not tactic['before'] or any(s['sourceText'] == tactic['sourceText'] and s['startLine'] == start for s in steps):
            continue
        if any(s['startLine'] <= start <= s['endLine'] for s in steps) and not tactic['sourceText'].lstrip().startswith(('have ', 'let ', 'induction ', 'cases ')):
            continue
        key = (start, end)
        if key in seen:
            continue
        seen.add(key)
        ident = f"{target['id']}.block-{start}-{sha256(tactic['sourceText'].encode())[:8]}"
        for phase in ('before', 'after'):
            for i, goal in enumerate(tactic[phase], 1):
                goal.setdefault('id', f'{ident}.{phase}.{i}')
        blocks.append(dict(id=ident, branch=f"{target['id']}.blocks",
                           label=tactic['sourceText'].splitlines()[0],
                           startLine=start, endLine=end, sourceText=tactic['sourceText'],
                           before=tactic['before'], after=tactic['after'],
                           kind='closure' if not tactic['after'] else 'continuation'))
    return {
        "id": target["id"],
        "declaration": target["declaration"],
        "source": {
            "commit": SOURCE_COMMIT,
            "path": target["path"],
            "sha256": sha256(source_bytes),
            "codeSha256": sha256(code.encode("utf-8")),
            "code": code,
            "startLine": declaration_range["start"]["line"],
            "endLine": declaration_range["end"]["line"],
        },
        "leanVersion": LEAN_VERSION,
        "steps": steps,
        # Parent tactic snapshots surround a complete nested block. They are
        # separate from the leaf timeline: never pretend they precede a child.
        "blocks": sorted(blocks, key=lambda s: (s['startLine'], s['endLine'])),
    }


def generate() -> bytes:
    assert_pins()
    legacy = json.loads(run(['git', 'show', f"{SPANISH_CONFIG['baseCommit']}:artifacts/explorer/proofs.json"], text=True).stdout)
    LEGACY_STEPS.update({proof['id']: proof['steps'] for proof in legacy['proofs']})
    # Foundation is a separate root; ensure its imported .olean files exist
    # even on a fresh CI checkout before the dynamic frontend loads them.
    run(["lake", "build", *sorted({target["module"] for target in TARGETS})])
    proofs = [make_proof(target) for target in TARGETS]
    exporter_hash = sha256((ROOT / "ProofExplorerExport.lean").read_bytes())
    document = {
        "schemaVersion": 1,
        "provenance": {
            "repositoryCommit": SOURCE_COMMIT,
            "leanToolchain": LEAN_TOOLCHAIN,
            "subversoRevision": SUBVERSO_REVISION,
            "exporterSourceHash": exporter_hash,
        },
        "proofs": proofs,
    }
    return (json.dumps(document, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check", action="store_true", help="fail unless the tracked artifact is fresh"
    )
    args = parser.parse_args()
    try:
        generated = generate()
        if args.check:
            if not OUTPUT.exists() or OUTPUT.read_bytes() != generated:
                raise ExportError(f"generated artifact is stale: {OUTPUT.relative_to(ROOT)}")
        else:
            OUTPUT.parent.mkdir(parents=True, exist_ok=True)
            OUTPUT.write_bytes(generated)
    except (ExportError, subprocess.CalledProcessError) as exc:
        print(f"proof explorer generation failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
