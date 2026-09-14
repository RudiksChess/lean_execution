import unittest
from unittest.mock import patch

from generate_proof_explorer import ExportError, normalized_steps


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
