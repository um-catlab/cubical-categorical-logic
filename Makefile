AGDA_BIN?=agda
AGDA_FLAGS?= -j10
AGDA_EXEC?=$(AGDA_BIN) $(AGDA_FLAGS)
RTS_OPTIONS=+RTS -M16G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)

.PHONY : all
all : build

.PHONY : build
build :
	$(MAKE) AGDA_EXEC=$(AGDA_BIN) check

.PHONY : check check-safe check-unsafe
check: check-safe check-unsafe

check-safe:
	cd safe && $(AGDA) --build-library

check-unsafe:
	cd unsafe && $(AGDA) --build-library

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete
