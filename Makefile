PYTHON ?= python3
.PHONY: verify certificates lean

# Certificates and the tests on their printed values (python-flint, about 6 minutes on a laptop).
verify:
	$(PYTHON) -m unittest discover -s tests -v

# The certificates alone, printing every claim.
certificates:
	cd certificates && $(PYTHON) derand_cert.py && $(PYTHON) certify_L1.py && $(PYTHON) certify_levers.py \
		&& $(PYTHON) certify.py && $(PYTHON) check_negtri.py \
		&& $(PYTHON) check_derand.py && $(PYTHON) check_derand_controls.py \
		&& $(PYTHON) stacked_cert.py && $(PYTHON) check_stacked.py \
		&& $(PYTHON) bands_cert.py && $(PYTHON) check_bands_rep.py && $(PYTHON) check_bands_carry.py \
		&& $(PYTHON) check_bands_stretch.py && $(PYTHON) check_bands_segments.py && $(PYTHON) check_bands_buckets.py \
		&& $(PYTHON) bands3_cert.py

# The Lean 4 kernel checks (lean/README.md): needs elan (Lean v4.34.1) and the Mathlib cache; about 13 min on 3 cores.
# Stacked.lean (folded all-edges Exact Triangle) and KClique.lean (its k-Clique corollary) add about 2 min.
# Bands2*.lean (the kernel check of certificates/bands_cert.py, Theorem 3) adds about 35 min on 2 cores.
# Bands3*.lean (the kernel check of certificates/bands3_cert.py, Theorem C') adds about 7 min on 2 cores.
lean:
	cd lean && lake exe cache get && lake build ThreesumLean ThreesumLean.Stacked ThreesumLean.KClique \
		ThreesumLean.Bands2 ThreesumLean.Bands3 && lake env lean ThreesumLean/Axioms.lean
