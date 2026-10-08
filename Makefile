.PHONY: all build-core build-stubs build-all ci lock-update lock-check cache-get clean

# Default target: run the full CI suite
all: ci

# Build Core with warnings treated as errors; theorem axioms need a separate audit.
build-core:
	lake build Bosonize

# Build the staging library (BosonizeStubs), which allows 'sorry' placeholders
build-stubs:
	lake build BosonizeStubs

# Build both Core and Stubs
build-all: build-core build-stubs

# Run guard tests, strict freeze verification, and both Lean library builds.
ci:
	./scripts/ci.sh

# Record reviewed declaration headers, definitions, instances, and context.
# Only run after human review; changed frozen content requires explicit acceptance.
lock-update:
	python3 scripts/guards/stub_lock.py --update

# Check the frozen content and reject new, unreviewed declarations/files.
lock-check:
	python3 scripts/guards/stub_lock.py --check --strict
	python3 scripts/guards/core_lock.py

# Fetch pre-compiled Mathlib binaries to avoid building Mathlib from scratch
cache-get:
	lake exe cache get

# Clean the build artifacts
clean:
	lake clean
