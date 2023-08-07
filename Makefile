.PHONY: run test
.DELETE_ON_ERROR:

TGT=app/Main

GHCOPTS=-prof
RTSOPTS=+RTS -xc

$(TGT): build

build:
	cabal build

interp:
	cabal repl

run: build
	 cabal run

include testing.mk
test: build vm
	$(MAKE) test_all

vm:
	$(MAKE) -C vm

test_clean:
	find tests/ok/ \( -name "*.actual*" -o -name "*.bc8" -o -name "*.check*" -o -name "*.fd4.c" -o -name "*.fd4.c.out" \) -exec rm {} \;
	@echo "Se eliminaron los archivos complementarios de test."

.PHONY: vm
