import unittest

from check_axioms import validate


class AxiomPolicyTests(unittest.TestCase):
    def test_allowed(self):
        validate("'T' depends on axioms: [propext, Classical.choice, Quot.sound]", {"T"})

    def test_no_axioms(self):
        validate("'T' does not depend on any axioms", {"T"})

    def test_subset(self):
        validate("'T' depends on axioms: [propext]", {"T"})

    def test_sorry_and_custom_axioms(self):
        for axiom in ("sorryAx", "oracle", "propext, oracle"):
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                validate(f"'T' depends on axioms: [{axiom}]", {"T"})

    def test_incomplete_or_malformed_output(self):
        for output in (
            "", "'U' does not depend on any axioms",
            "'T' does not depend on any axioms\n'T' does not depend on any axioms",
            "warning: declaration uses sorry", "'T' depends on axioms: [propext,]",
        ):
            with self.subTest(output=output), self.assertRaises(ValueError):
                validate(output, {"T"})


if __name__ == "__main__":
    unittest.main()
