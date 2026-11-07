.PHONY: tests verify docs figures confirmation
# Run from the extracted package root with GNU make.
tests:
	python3 run.py --tests --extended
verify:
	python3 run.py --all --diagnostics
docs:
	python3 scripts/build_docs.py --compile
figures:
	python3 scripts/build_docs.py --compile --figures
confirmation:
	python3 confirm.py --check
