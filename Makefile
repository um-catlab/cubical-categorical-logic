AGDA = agda
FIX_WHITESPACE = fix-whitespace

# Finds all .agda files in the current directory and subdirectories
FIND_AGDA_FILES = find . -name "*.agda"
AGDA_FILES = $(shell $(FIND_AGDA_FILES))

# The targets are the .agdai files corresponding to the .agda files
AGDAI_FILES = $(AGDA_FILES:.agda=.agdai)

.PHONY: test
test: Everything.agda check-whitespace
	$(AGDA) $<

.PHONY: test-and-report
test-and-report:
	@failed=""; \
	for file in $(AGDA_FILES); do \
		$(AGDA) $$file || failed="$$failed $$file"; \
	done; \
	[ -z "$$failed" ] || (echo "Failed to compile:$$failed" && false)

.PHONY: check-whitespace
check-whitespace:
	$(FIX_WHITESPACE) --check

# modified from
# https://github.com/agda/agda-categories/blob/dc2a5bd7ad39b0629b21763884b8e85a96111981/Makefile#L14
#
# NOTES:
# sed: we're using Basic Regular Expression (BRE) syntax
# sort: LC_ALL=C for a deterministic order
# PHONY in case agda files are created/deleted
.PHONY: Everything.agda
Everything.agda:
	$(FIND_AGDA_FILES) ! -path './$@' | sed -e 's#/#.#g' -e 's/^\.*//' -e 's/.agda$$//' -e 's/^/import /' | LC_ALL=C sort > $@

.PHONY: clean
clean:
	find . -name "*.agdai" -type f -delete
	-rm Everything.agda
