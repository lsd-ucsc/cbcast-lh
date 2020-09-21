# this file assumes you're already in a nix-shell
#
# this file build using setup commands (not nix-build)

CONFIG_FILE = dist/setup-config
CABAL_FILE = cbcast-in-lh.cabal
SETUP_CMD = runhaskell -hide-package=base Setup.hs

.PHONY: test build clean repl

test: build
	$(SETUP_CMD) test

# TODO use dist/build/%/% ? scan cabalfile for executable names?
build: $(CONFIG_FILE)
	$(SETUP_CMD) build

$(CONFIG_FILE): $(CABAL_FILE)
	$(SETUP_CMD) configure --enable-tests

clean: $(CABAL_FILE)
	$(SETUP_CMD) clean
	rm -v $(CABAL_FILE)

%.cabal:
	hpack

## tools

repl: $(CONFIG_FILE)
	$(SETUP_CMD) repl $(basename $(CABAL_FILE))

ghcid:
	ghcid -c make repl
entr-build:
	git ls-files | entr -c bash -c 'make build; echo done'
entr-test:
	git ls-files | entr -c bash -c 'make test; echo done'
