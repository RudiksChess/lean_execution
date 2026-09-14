import unittest
from unittest.mock import patch

from generate_proof_explorer import ExportError, normalized_steps, general_steps


def raw_step(*, line=1, before=None, after=None):
    return {
        "proof": {
            "tactics": [
                {
                    "syntaxKind": "Lean.Parser.Tactic.intro",
                    "range": {
                        "start": {"line": line, "column": 1},
                        "end": {"line": line, "column": 6},
                    },
                    "sourceText": "intro x",
                    "before": [{"hypotheses": [], "target": "P"}]
                    if before is None
                    else before,
                    "after": [] if after is None else after,
                }
            ]
        }
    }


class ProofExplorerNormalizationTests(unittest.TestCase):
    def test_general_export_drops_tokens_and_wrappers_not_tactics(self):
        tactic = raw_step()["proof"]["tactics"][0]
        tactic["range"].update(startByte=10, endByte=17)
        token = {**tactic, "syntaxKind": "ident", "sourceText": "x",
                 "range": {**tactic["range"], "startByte": 16}}
        wrapper = {**tactic, "syntaxKind": "Lean.Parser.Tactic.tacticSeq",
                   "range": {**tactic["range"], "startByte": 0}}
        steps = general_steps("fixture", {"proof": {"tactics": [wrapper, tactic, token]}})
        self.assertEqual(len(steps), 1)
        self.assertEqual(steps[0]["sourceText"], "intro x")

    def test_general_export_keeps_nested_local_proof_without_summary_closure(self):
        inner = raw_step()["proof"]["tactics"][0]
        inner["range"].update(startByte=10, endByte=17)
        outer = {**inner, "syntaxKind": "Lean.Parser.Tactic.tacticHave__",
                 "sourceText": "have h := by intro x",
                 "range": {**inner["range"], "startByte": 0, "endByte": 20}}
        result = general_steps("fixture", {"proof": {"tactics": [outer, inner]}})
        self.assertEqual([s["sourceText"] for s in result], ["intro x"])

    def test_general_export_requires_real_tactics(self):
        with self.assertRaises(ExportError):
            general_steps("fixture", {"proof": {"tactics": []}})

    def test_anonymous_goal_gets_stable_presentation_id(self):
        with patch.dict(
            "generate_proof_explorer.EXPECTED",
            {"fixture": [("fixture.case.close", "fixture.case", 1)]},
        ):
            steps = normalized_steps("fixture", raw_step())
        self.assertEqual(
            steps[0]["before"][0]["id"],
            "fixture.case.close.before.goal-1",
        )
        self.assertEqual(steps[0]["kind"], "closure")

    def test_named_goal_is_preserved(self):
        before = [{"id": "actualCase", "hypotheses": [], "target": "P"}]
        with patch.dict(
            "generate_proof_explorer.EXPECTED",
            {"fixture": [("fixture.case.close", "fixture.case", 1)]},
        ):
            steps = normalized_steps("fixture", raw_step(before=before))
        self.assertEqual(steps[0]["before"][0]["id"], "actualCase")

    def test_missing_before_state_fails_closed(self):
        with patch.dict(
            "generate_proof_explorer.EXPECTED",
            {"fixture": [("fixture.case.close", "fixture.case", 1)]},
        ), self.assertRaises(ExportError):
            normalized_steps("fixture", raw_step(before=[]))

    def test_source_range_drift_fails_closed(self):
        with patch.dict(
            "generate_proof_explorer.EXPECTED",
            {"fixture": [("fixture.case.close", "fixture.case", 1)]},
        ), self.assertRaises(ExportError):
            normalized_steps("fixture", raw_step(line=2))

    def test_missing_tactic_fails_closed(self):
        with patch.dict(
            "generate_proof_explorer.EXPECTED",
            {"fixture": [("fixture.case.close", "fixture.case", 1)]},
        ), self.assertRaises(ExportError):
            normalized_steps("fixture", {"proof": {"tactics": []}})

    def test_missing_following_state_fails_closed(self):
        with patch.dict(
            "generate_proof_explorer.EXPECTED",
            {"fixture": [("fixture.case.intro", "fixture.case", 1)]},
        ), self.assertRaises(ExportError):
            normalized_steps("fixture", raw_step(after=[]))


if __name__ == "__main__":
    unittest.main()
