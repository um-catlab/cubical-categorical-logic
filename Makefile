AGDA = agda
FIX_WHITESPACE = fix-whitespace

# Finds all .agda files in the current directory and subdirectories
AGDA_FILES = $(shell find Cubical -name "*.agda")

# The targets are the .agdai files corresponding to the .agda files
AGDAI_FILES = $(AGDA_FILES:.agda=.agdai)

all: $(AGDAI_FILES)

test: check-whitespace $(AGDAI_FILES)

test-and-report:
	@failed=""; \
	for file in $(AGDA_FILES); do \
		$(AGDA) $$file || failed="$$failed $$file"; \
	done; \
	[ -z "$$failed" ] || (echo "Failed to compile:$$failed" && false)

.PHONY: check-whitespace
check-whitespace:
	$(FIX_WHITESPACE) --check

%.agdai: %.agda
	$(AGDA) $<

clean:
	find . -name "*.agdai" -type f -delete

.PHONY: all clean test
