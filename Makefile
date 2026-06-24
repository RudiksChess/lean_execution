.PHONY: build audit pdf check clean

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

# CI gate: proofs build and the committed audit still matches reality.
# Fails if a sorry (sorryAx) or rogue axiom sneaks in, or audit.txt drifts.
check: build audit
	git diff --exit-code audit.txt

clean:
	latexmk -C ThesisReport_ND.tex
