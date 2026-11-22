"""Tests for the theory mode (`--theory`) of the proof-explorer generator.

The fixture tests exercise the normalization without Lean. The artifact tests
read the tracked `artifacts/explorer/theory.json` and compare its shape with
`artifacts/explorer/proofs.json`; `make proof-explorer-theory-check` is what
proves that the tracked file is what Lean produces.
"""

import hashlib
import json
import unittest

from generate_proof_explorer import (
    ExportError,
    OUTPUT,
    ROOT,
    THEORY_EXPORTER,
    THEORY_MODULES,
    THEORY_OUTPUT,
    THEORY_SOURCE_COMMIT,
    theory_steps,
    theory_targets,
)


def goal(target="P"):
    return {"hypotheses": [], "target": target}


def tactic(kind, text, start_byte, end_byte, *, line=3, end_line=None, before=None, after=None):
    return {
        "syntaxKind": kind,
        "sourceText": text,
        "range": {
            "start": {"line": line, "column": 1},
            "end": {"line": line if end_line is None else end_line, "column": 2},
            "startByte": start_byte,
            "endByte": end_byte,
        },
        "before": [goal()] if before is None else before,
        "after": [] if after is None else after,
    }


def term(text="⟨a, b⟩", *, before=None):
    return {
        "syntaxKind": "Lean.Parser.Term.anonymousCtor",
        "sourceText": text,
        "range": {"start": {"line": 2, "column": 3}, "end": {"line": 2, "column": 9},
                  "startByte": 20, "endByte": 26},
        "before": [goal("A ∧ B")] if before is None else before,
    }


class TheoryNormalizationTests(unittest.TestCase):
    def test_targets_are_the_69_unique_full_names(self):
        targets = theory_targets()
        ids = [target["id"] for target in targets]
        self.assertEqual(len(ids), 69)
        self.assertEqual(len(set(ids)), 69)
        for target in targets:
            self.assertEqual(target["id"], target["declaration"])
            self.assertTrue(target["id"].startswith(target["module"] + "."))
            self.assertEqual(target["path"], target["module"].replace(".", "/") + ".lean")
        self.assertIn("Thesis.Teoria.Lambda.lema_7_6", ids)
        self.assertIn("Thesis.Teoria.Cubo.LambdaOmega.derivacion_completa", ids)

    def test_term_body_becomes_one_term_step_with_the_elaborator_goal(self):
        steps, blocks = theory_steps("T.x", {"tactics": [], "term": term()})
        self.assertEqual(blocks, [])
        self.assertEqual(len(steps), 1)
        step = steps[0]
        self.assertEqual(step["id"], "T.x.term")
        self.assertEqual(step["kind"], "term")
        self.assertEqual(step["after"], [])
        self.assertEqual(step["before"][0]["target"], "A ∧ B")
        self.assertEqual(step["before"][0]["id"], "T.x.term.before.goal-1")
        self.assertEqual((step["startLine"], step["endLine"]), (2, 2))

    def test_term_body_without_recorded_state_fails_closed(self):
        with self.assertRaises(ExportError):
            theory_steps("T.x", {"tactics": [], "term": term(before=[])})

    def test_tactic_proof_without_tactic_states_fails_closed(self):
        with self.assertRaises(ExportError):
            theory_steps("T.x", {"tactics": [], "term": None})

    def test_theory_only_tactic_kind_is_a_step(self):
        ext = tactic("Lean.Elab.Tactic.Ext.ext", "ext y", 10, 15, after=[goal("Q")])
        steps, _ = theory_steps("T.x", {"tactics": [ext], "term": None})
        self.assertEqual([step["sourceText"] for step in steps], ["ext y"])
        self.assertEqual(steps[0]["kind"], "continuation")

    def test_wrapper_of_a_nested_tactic_block_is_kept_as_block(self):
        outer = tactic("Lean.Parser.Tactic.exact", "exact h (by simp)", 10, 27)
        inner = tactic("Lean.Parser.Tactic.simp", "simp", 22, 26)
        steps, blocks = theory_steps("T.x", {"tactics": [outer, inner], "term": None})
        self.assertEqual([step["sourceText"] for step in steps], ["simp"])
        self.assertEqual([block["sourceText"] for block in blocks], ["exact h (by simp)"])


class TheoryArtifactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.theory = json.loads(THEORY_OUTPUT.read_text(encoding="utf-8"))
        cls.practice = json.loads(OUTPUT.read_text(encoding="utf-8"))

    def test_serialization_is_canonical(self):
        data = THEORY_OUTPUT.read_bytes()
        expected = (json.dumps(self.theory, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
        self.assertEqual(data, expected)

    def test_all_69_ids_present_and_unique(self):
        ids = [proof["id"] for proof in self.theory["proofs"]]
        self.assertEqual(ids, [target["id"] for target in theory_targets()])
        self.assertEqual(len(set(ids)), 69)
        for proof in self.theory["proofs"]:
            self.assertEqual(proof["id"], proof["declaration"])
        state_ids = [state["id"] for proof in self.theory["proofs"]
                     for state in proof["steps"] + proof["blocks"]]
        self.assertEqual(len(state_ids), len(set(state_ids)))

    def test_provenance_and_sources_are_pinned(self):
        provenance = self.theory["provenance"]
        self.assertEqual(provenance["repositoryCommit"], THEORY_SOURCE_COMMIT)
        self.assertEqual(
            provenance["exporterSourceHash"],
            hashlib.sha256((ROOT / THEORY_EXPORTER).read_bytes()).hexdigest(),
        )
        pinned = {entry["module"].replace(".", "/") + ".lean": entry["sha256"]
                  for entry in THEORY_MODULES}
        for proof in self.theory["proofs"]:
            source = proof["source"]
            self.assertEqual(source["commit"], THEORY_SOURCE_COMMIT)
            self.assertEqual(source["sha256"], pinned[source["path"]])
            lines = (ROOT / source["path"]).read_text(encoding="utf-8").split("\n")
            self.assertEqual(
                "\n".join(lines[source["startLine"] - 1:source["endLine"]]), source["code"]
            )
            self.assertEqual(
                source["codeSha256"], hashlib.sha256(source["code"].encode("utf-8")).hexdigest()
            )

    def test_every_state_lies_inside_its_declaration(self):
        for proof in self.theory["proofs"]:
            source = proof["source"]
            for state in proof["steps"] + proof["blocks"]:
                self.assertLessEqual(source["startLine"], state["startLine"], state["id"])
                self.assertLessEqual(state["startLine"], state["endLine"], state["id"])
                self.assertLessEqual(state["endLine"], source["endLine"], state["id"])

    def test_every_state_has_a_real_goal_before(self):
        for proof in self.theory["proofs"]:
            self.assertTrue(proof["steps"], proof["id"])
            for state in proof["steps"] + proof["blocks"]:
                self.assertTrue(state["before"], state["id"])
                for goal_ in state["before"] + state["after"]:
                    self.assertTrue(goal_["target"], state["id"])
                    self.assertTrue(goal_["id"], state["id"])

    def test_term_steps_are_declared_and_only_lead_term_bodies(self):
        term_proofs = 0
        for proof in self.theory["proofs"]:
            kinds = [step["kind"] for step in proof["steps"]]
            self.assertLessEqual(set(kinds), {"term", "continuation", "closure"})
            self.assertLessEqual({block["kind"] for block in proof["blocks"]},
                                 {"continuation", "closure"})
            if "term" in kinds:
                term_proofs += 1
                self.assertEqual(kinds.count("term"), 1)
                self.assertEqual(kinds[0], "term")
                self.assertEqual(proof["steps"][0]["id"], proof["id"] + ".term")
                self.assertEqual(proof["steps"][0]["after"], [])
                self.assertNotIn(":= by\n", proof["source"]["code"])
            for step in proof["steps"]:
                if step["kind"] == "closure":
                    self.assertEqual(step["after"], [])
                if step["kind"] == "continuation":
                    self.assertTrue(step["after"])
        self.assertEqual(term_proofs, 21)

    def test_schema_parity_with_proofs_json(self):
        def keys(items):
            return {frozenset(item) for item in items}

        self.assertEqual(set(self.theory), set(self.practice))
        self.assertEqual(self.theory["schemaVersion"], self.practice["schemaVersion"])
        self.assertEqual(set(self.theory["provenance"]), set(self.practice["provenance"]))
        for name in ("leanToolchain", "subversoRevision"):
            self.assertEqual(self.theory["provenance"][name], self.practice["provenance"][name])
        theory, practice = self.theory["proofs"], self.practice["proofs"]
        self.assertEqual(keys(theory), keys(practice))
        self.assertEqual(keys(p["source"] for p in theory), keys(p["source"] for p in practice))
        self.assertEqual({p["leanVersion"] for p in theory}, {p["leanVersion"] for p in practice})
        for field in ("steps", "blocks"):
            self.assertEqual(keys(s for p in theory for s in p[field]),
                             keys(s for p in practice for s in p[field]))
        goals = lambda proofs: [g for p in proofs for s in p["steps"] + p["blocks"]
                                for g in s["before"] + s["after"]]
        self.assertEqual(keys(goals(theory)), keys(goals(practice)))
        self.assertEqual(keys(h for g in goals(theory) for h in g["hypotheses"]),
                         keys(h for g in goals(practice) for h in g["hypotheses"]))


if __name__ == "__main__":
    unittest.main()
