.PHONY: build audit audit-quicksort verification-output proof-explorer proof-explorer-check pdf pdf-quicksort pdf-aristotle check clean verify-foundation verify-aristotle docs

ND_DIR := reports/natural-deduction
QS_DIR := reports/quicksort
AR_DIR := reports/aristotle
VERIFY_OUTPUT := web/lean-output.txt

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

# Generate the public, plain-text Lean transcript shown on the verification
# page. The theorem types, evaluations, and axiom lists are emitted by Lean.
verification-output:
	@{ \
		echo 'Lean 4 public verification transcript'; \
		echo '====================================='; \
		echo; \
		echo '$$ cat lean-toolchain'; \
		cat lean-toolchain; \
		echo; \
		echo '$$ lake env lean Thesis/VerificationOutput.lean'; \
		lake env lean Thesis/VerificationOutput.lean; \
	} > $(VERIFY_OUTPUT)

# Generate real tactic states for the public proof explorer. The Lean adapter is
# a separate executable and is not imported by the core Thesis library.
proof-explorer:
	python3 tools/generate_proof_explorer.py

# Fresh elaboration must reproduce the tracked artifact byte-for-byte.
proof-explorer-check:
	python3 tools/generate_proof_explorer.py --check

# Build the natural-deduction thesis PDF (regenerating the audit first).
pdf: audit
	cd $(ND_DIR) && latexmk -pdf -interaction=nonstopmode ThesisReport_ND.tex

# Build the quicksort report PDF (regenerating its audit first).
pdf-quicksort: audit-quicksort
	cd $(QS_DIR) && latexmk -pdf -interaction=nonstopmode QuicksortReport.tex

# Build the Aristotle proofs reference PDF. Listings are pulled from the
# aristotle/ source by anchor range; the markers are hidden, so the chunks show
# Aristotle's output verbatim.
pdf-aristotle:
	cd $(AR_DIR) && latexmk -pdf -interaction=nonstopmode AristotleProofs.tex

# Type-check the standalone Aristotle case-study files (AI cross-validation).
# Not part of the lake build (they re-declare the calculus in their own units).
verify-aristotle:
	lake env lean aristotle/NDCore.lean
	lake env lean aristotle/NDFull.lean
	lake env lean aristotle/QuicksortFull.lean

# Build the independent Foundation cross-validation as a separate root. It
# cannot share one root module with the full Mathlib closure (both define
# Matrix.map), but it is still part of the public verification gate.
verify-foundation:
	lake build Thesis.Prop.CompletenessViaFoundation

# CI gate: both developments and both cross-validations build, and the
# committed audit still matches reality.
# Fails if a sorry (sorryAx) or rogue axiom sneaks in, or the audit drifts.
check: build audit audit-quicksort verification-output proof-explorer-check verify-foundation verify-aristotle
	python3 -m unittest discover -s tools -p 'test_*.py'
	python3 tools/check_axioms.py
	git diff --exit-code $(ND_DIR)/audit.txt $(QS_DIR)/audit.txt $(VERIFY_OUTPUT)

# Browsable API docs (doc-gen4). Heavy: builds HTML for the full import closure.
# Output: docbuild/.lake/build/doc/index.html
docs:
	cd docbuild && lake exe cache get && lake build Thesis:docs
	@echo "Open docbuild/.lake/build/doc/index.html"

clean:
	cd $(ND_DIR) && latexmk -C ThesisReport_ND.tex
	cd $(QS_DIR) && latexmk -C QuicksortReport.tex
