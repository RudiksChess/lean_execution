.PHONY: build audit pdf check clean verify-aristotle

# Build the verified Lean development (pulls the Mathlib cache first).
build:
	lake exe cache get
	lake build

# Regenerate the axiom certificate from the actual proofs.
# The thesis includes audit.txt verbatim via \lstinputlisting.
audit:
	lake env lean Thesis/Prop/Audit.lean > audit.txt

# Build the thesis PDF (regenerating the audit first).
pdf: audit
	latexmk -pdf -interaction=nonstopmode ThesisReport_ND.tex

# Type-check the standalone Aristotle case-study files (Section: AI cross-validation).
# Not part of the lake build (they re-declare the calculus in their own units).
verify-aristotle:
	lake env lean aristotle/NDCore.lean
	lake env lean aristotle/NDFull.lean

# CI gate: proofs build, the committed audit still matches reality, and the
# AI-generated case-study proofs still compile.
# Fails if a sorry (sorryAx) or rogue axiom sneaks in, or audit.txt drifts.
check: build audit verify-aristotle
	git diff --exit-code audit.txt

clean:
	latexmk -C ThesisReport_ND.tex
