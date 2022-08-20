# this file assumes you're already in a nix-shell
#
# this file build using setup commands (not nix-build)

CONFIG_FILE = dist/setup-config
CABAL_FILE = cbcast-lh.cabal
SETUP_CMD = runhaskell -hide-package=base Setup.hs

HS_FILES_CMD = find . -name '*hs'
# command to detect LH escapehatches
ESCAPES_CMD = grep --color=always '==!\|Admit\|undefined\|--check-var\|--skip-module' $$($(HS_FILES_CMD))
# command to detect programmer tasks
MESSES_CMD = grep --color=always 'TODO\|FIXME\|XXX\|QQQ\|NOTE\|MIGRATION' $$($(HS_FILES_CMD))

.PHONY: test build clean repl

test: build
	time $(SETUP_CMD) test

# TODO use dist/build/%/% ? scan cabalfile for executable names?
build: $(CONFIG_FILE)
	time $(SETUP_CMD) build

$(CONFIG_FILE): $(CABAL_FILE)
	$(SETUP_CMD) configure --enable-tests

check: clean
	if $(ESCAPES_CMD); then \
		echo Found banned identifiers; false; \
	fi
	make build

clean: $(CABAL_FILE)
	$(SETUP_CMD) clean
	rm -v $(CABAL_FILE)
	-find . -name '.liquid' -exec rm -rfv '{}' \;

%.cabal: package.yaml
	hpack

## tools

repl: $(CONFIG_FILE)
	$(SETUP_CMD) repl $(basename $(CABAL_FILE))

ghcid:
	nix-shell -p ghcid --run 'ghcid -c make repl'
entr-build:
	git ls-files | entr -c bash -c 'make build'
entr-test:
	git ls-files | entr -c bash -c 'make test'

escapes:
	$(ESCAPES_CMD)

messes:
	$(MESSES_CMD)
