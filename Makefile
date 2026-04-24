AGDA_BIN?=agda
AGDA_FLAGS?= -j10
AGDA_EXEC?=$(AGDA_BIN) $(AGDA_FLAGS)
FIX_WHITESPACE?=fix-whitespace
RTS_OPTIONS=+RTS -M16G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)
RUNHASKELL?=runhaskell

# Finds all .agda files in the current directory and subdirectories
FIND_AGDA_FILES = find . -name "*.agda"
AGDA_FILES = $(shell $(FIND_AGDA_FILES))

# The targets are the .agdai files corresponding to the .agda files
AGDAI_FILES = $(AGDA_FILES:.agda=.agdai)
.PHONY : all
all : build

.PHONY : build
build :
	$(MAKE) AGDA_EXEC=$(AGDA_BIN) check

.PHONY : test
test : check-whitespace check

.PHONY : check
check:
	$(AGDA) --build-library

# checking and fixing whitespace

.PHONY : fix-whitespace
fix-whitespace:
	$(FIX_WHITESPACE)

.PHONY : check-whitespace
check-whitespace:
	$(FIX_WHITESPACE) --check

.PHONY : listings
listings:
	./generate-everything.sh > Everything.agda
	$(AGDA) Everything.agda -i. -isrc --html -vhtml:0
	cp -f html/Everything.html html/index.html

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete

.PHONY: debug
debug : ## Print debug information.
	@echo "AGDA_BIN              = $(AGDA_BIN)"
	@echo "AGDA_FLAGS            = $(AGDA_FLAGS)"
	@echo "AGDA_EXEC             = $(AGDA_EXEC)"
	@echo "AGDA                  = $(AGDA)"

.PHONY: check-line-lengths
check-line-lengths:
	bash check-line-lengths.sh
