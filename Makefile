.PHONY: build audit audit-quicksort pdf pdf-quicksort pdf-aristotle check clean verify-aristotle docs

ND_DIR := reports/natural-deduction
QS_DIR := reports/quicksort
AR_DIR := reports/aristotle

# Build both verified developments — Thesis.Prop (completeness) and
# Thesis.Sort (quicksort) — pulling the Mathlib cache first.
build:
	lake exe cache get
	lake build

# Regenerate the axiom certificate for the natural-deduction development.
# The ND report includes this verbatim via \lstinputlisting.
audit:
	lake env lean Thesis/Prop/Audit.lean > $(ND_DIR)/audit.txt

# Regenerate the axiom certificate for the quicksort development.
audit-quicksort:
	lake env lean Thesis/Sort/Audit.lean > $(QS_DIR)/audit.txt

# Build the natural-deduction thesis PDF (regenerating the audit first).
pdf: audit
	cd $(ND_DIR) && latexmk -pdf -interaction=nonstopmode ThesisReport_ND.tex

# Build the quicksort report PDF (regenerating its audit first).
pdf-quicksort: audit-quicksort
	cd $(QS_DIR) && latexmk -pdf -interaction=nonstopmode QuicksortReport.tex

# Build the Aristotle proofs reference PDF. Strips the report-only anchor
# comments so the listings show Aristotle's output verbatim.
pdf-aristotle:
	mkdir -p $(AR_DIR)/_src
	for f in NDCore NDFull QuicksortFull; do \
	  grep -v -- '-- ANCHOR' aristotle/$$f.lean > $(AR_DIR)/_src/$$f.lean; \
	done
	cd $(AR_DIR) && latexmk -pdf -interaction=nonstopmode AristotleProofs.tex

# Type-check the standalone Aristotle case-study files (AI cross-validation).
# Not part of the lake build (they re-declare the calculus in their own units).
verify-aristotle:
	lake env lean aristotle/NDCore.lean
	lake env lean aristotle/NDFull.lean
	lake env lean aristotle/QuicksortFull.lean

# CI gate: both developments build, the committed audit still matches reality,
# and the AI case-study proofs still compile.
# Fails if a sorry (sorryAx) or rogue axiom sneaks in, or the audit drifts.
check: build audit audit-quicksort verify-aristotle
	git diff --exit-code $(ND_DIR)/audit.txt $(QS_DIR)/audit.txt

# Browsable API docs (doc-gen4). Heavy: builds HTML for the full import closure.
# Output: docbuild/.lake/build/doc/index.html
docs:
	cd docbuild && lake exe cache get && lake build Thesis:docs
	@echo "Open docbuild/.lake/build/doc/index.html"

clean:
	cd $(ND_DIR) && latexmk -C ThesisReport_ND.tex
	cd $(QS_DIR) && latexmk -C QuicksortReport.tex
