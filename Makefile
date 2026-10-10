PYTHON ?= python3
.PHONY: verify certificates lean

# Certificates and the tests on their printed values (python-flint, seconds on a laptop).
verify:
	$(PYTHON) -m unittest discover -s tests -v

# The certificates alone, printing every claim.
certificates:
	cd certificates && $(PYTHON) derand_cert.py && $(PYTHON) certify_L1.py && $(PYTHON) certify_levers.py \
		&& $(PYTHON) certify.py && $(PYTHON) check_negtri.py \
		&& $(PYTHON) check_derand.py && $(PYTHON) check_derand_controls.py

# The Lean 4 kernel checks (lean/README.md): needs elan (Lean v4.34.1) and the Mathlib cache; about 13 min on 3 cores.
# Stacked.lean (folded all-edges Exact Triangle) and KClique.lean (its k-Clique corollary) add about 2 min.
lean:
	cd lean && lake exe cache get && lake build ThreesumLean ThreesumLean.Stacked ThreesumLean.KClique \
		&& lake env lean ThreesumLean/Axioms.lean
