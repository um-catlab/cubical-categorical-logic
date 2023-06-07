AGDA = agda

# Finds all .agda files in the current directory and subdirectories
AGDA_FILES = $(shell find . -name "*.agda")

# The targets are the .agdai files corresponding to the .agda files
AGDAI_FILES = $(AGDA_FILES:.agda=.agdai)

all: $(AGDAI_FILES)

test: $(AGDAI_FILES)
	make clean

test-and-report:
	@failed=""; \
	for file in $(AGDA_FILES); do \
		$(AGDA) $$file || failed="$$failed $$file"; \
	done; \
	[ -z "$$failed" ] || (echo "Failed to compile:$$failed" && false)

%.agdai: %.agda
	$(AGDA) $<

clean:
	find . -name "*.agdai" -type f -delete

.PHONY: all clean test
