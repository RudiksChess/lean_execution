.PHONY: build audit pdf pdf-quicksort check clean verify-aristotle docs

ND_DIR := reports/natural-deduction
QS_DIR := reports/quicksort

# Build both verified developments — Thesis.Prop (completeness) and
# Thesis.Sort (quicksort) — pulling the Mathlib cache first.
build:
	lake exe cache get
	lake build

# Regenerate the axiom certificate for the natural-deduction development.
# The ND report includes this verbatim via \lstinputlisting.
audit:
	lake env lean Thesis/Prop/Audit.lean > $(ND_DIR)/audit.txt

# Build the natural-deduction thesis PDF (regenerating the audit first).
pdf: audit
	cd $(ND_DIR) && latexmk -pdf -interaction=nonstopmode ThesisReport_ND.tex

# Build the quicksort report PDF.
pdf-quicksort:
	cd $(QS_DIR) && latexmk -pdf -interaction=nonstopmode QuicksortReport.tex

# Type-check the standalone Aristotle case-study files (AI cross-validation).
# Not part of the lake build (they re-declare the calculus in their own units).
verify-aristotle:
	lake env lean aristotle/NDCore.lean
	lake env lean aristotle/NDFull.lean

# CI gate: both developments build, the committed audit still matches reality,
# and the AI case-study proofs still compile.
# Fails if a sorry (sorryAx) or rogue axiom sneaks in, or the audit drifts.
check: build audit verify-aristotle
	git diff --exit-code $(ND_DIR)/audit.txt

# Browsable API docs (doc-gen4). Heavy: builds HTML for the full import closure.
# Output: docbuild/.lake/build/doc/index.html
docs:
	cd docbuild && lake exe cache get && lake build Thesis:docs
	@echo "Open docbuild/.lake/build/doc/index.html"

clean:
	cd $(ND_DIR) && latexmk -C ThesisReport_ND.tex
	cd $(QS_DIR) && latexmk -C QuicksortReport.tex
