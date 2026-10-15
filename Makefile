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

# Self-service candidates. TARGETS/PROPOSAL are repository-relative paths.
.PHONY: help verify-a verify-b verify-c test-webllm
help:
	@echo 'build-core / build-stubs / build-all / ci / lock-check / lock-update / cache-get / clean'
	@echo 'verify-a PROPOSAL=docs/webllm/drafts/task.md (compile + data axiom audit)'
	@echo 'verify-b TARGETS="BosonizeStubs/Module.lean ..." (fresh proof/dependency axiom audit)'
	@echo 'verify-c PROPOSAL=docs/webllm/drafts/task.md (Markdown structure only)'
	@echo 'audit-data / audit-axioms TARGETS="path/to/Module.lean ..." (fresh import-based axiom output)'
	@echo 'test-webllm (verifier regression tests)'
	@echo 'Automated cycle: make lean-start-phaseB 18 / make lean-finish-phaseB 18 (also A/C)'
	@echo 'Per-theorem route (run in the hub): make api-prove-file FILE=BosonizeStubs/X.lean; make api-assemble FILE=... CHAPTER=N'
verify-a:
	@test -n "$(PROPOSAL)" || { echo 'Set PROPOSAL=path.md'; exit 2; }
	@python3 scripts/webllm/verify_phase_a.py "$(PROPOSAL)"
verify-b:
	@test -n "$(TARGETS)" || { echo 'Set TARGETS="BosonizeStubs/Module.lean ..."'; exit 2; }
	@python3 scripts/webllm/verify_phase_b.py $(TARGETS)
verify-c:
	@test -n "$(PROPOSAL)" || { echo 'Set PROPOSAL=path.md'; exit 2; }
	@python3 scripts/webllm/verify_phase_c.py "$(PROPOSAL)"
test-webllm:
	@python3 -m unittest discover -s scripts/webllm -p 'test_*.py' -v

.PHONY: audit-data audit-axioms
audit-data:
	@test -n "$(TARGETS)" || { echo 'Set TARGETS="BosonizeStubs/Module.lean ..."'; exit 2; }
	@python3 scripts/webllm/audit_axioms.py --data-only $(TARGETS)
audit-axioms:
	@test -n "$(TARGETS)" || { echo 'Set TARGETS="Bosonize/Core/Module.lean ..."'; exit 2; }
	@python3 scripts/webllm/audit_axioms.py $(TARGETS)

# Shared one-command chapter cycle, also available from this repository.
# Start commands print the absolute packet path and a "Send the file ... to ChatGPT" message.
LEAN_CYCLE_REPO := $(CURDIR)
# Resolve through the primary Git checkout so isolated worktrees also find the hub.
# Standalone clones retain ordinary build/CI commands when the hub is unavailable.
LEAN_CYCLE_HUB ?= $(abspath $(shell git rev-parse --git-common-dir)/../../..)
-include $(LEAN_CYCLE_HUB)/scripts/lean_cycle.mk
-include $(LEAN_CYCLE_HUB)/scripts/work.mk
