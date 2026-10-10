PYTHON ?= python3
.PHONY: verify certificates

# Certificates and the tests on their printed values (python-flint, seconds on a laptop).
verify:
	$(PYTHON) -m unittest discover -s tests -v

# The certificates alone, printing every claim.
certificates:
	cd certificates && $(PYTHON) derand_cert.py && $(PYTHON) certify_L1.py && $(PYTHON) certify_levers.py \
		&& $(PYTHON) certify.py && $(PYTHON) check_negtri.py \
		&& $(PYTHON) check_derand.py && $(PYTHON) check_derand_controls.py

