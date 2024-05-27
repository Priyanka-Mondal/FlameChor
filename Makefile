# makefile setup from https://www.reddit.com/r/haskell/comments/1132boo/comment/j9urqrf/?utm_source=share&utm_medium=web2x&context=3
makefile_dir := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
export PATH := $(makefile_dir):$(PATH)

project_name ?= flame
project_main ?= src/Flame/Solver.hs
retag_file ?= $(project_main)

stack.yaml:
	@test -f stack.yaml || (echo -e "This makefile requires a 'stack.yaml' for your project.\nYou don't need to use 'stack' to build your project.\nYou just need a 'stack.yaml' specifying a resolver compatible with your GHC version.\nSee https://www.stackage.org/" && exit 1)

stack: stack.yaml
	@which stack || (echo -e "This makefile requires 'stack' to be on your path. Use GHCup to install it.\nSee https://www.haskell.org/ghcup/" && exit 1)
.PHONY: stack

warning.txt:
	-@uname -a | grep -q Darwin && echo "WARNING: On Mac, you must alias 'make' to 'gmake' in your shell config file (e.g. ~/.bashrc or ~/.zshrc). Symbolic links will not work." | tee warning.txt
	@echo "Add 'warning.txt' to your .gitignore file if you never want to see this message again."

hasktags: warning.txt stack
	@echo 'stack exec -- hasktags' > hasktags
	@chmod +x hasktags
	@echo "You might like to add 'hasktags' to your .gitignore file."

tags: warning.txt hasktags stack
	@stack exec -- haskdogs
.PHONY: tags

retag: warning.txt stack
	@stack exec -- haskdogs -i $(retag_file) --hasktags-args "-x -c -a" | sort -u -o tags tags
.PHONY: retag

hpack: stack
	@stack setup
.PHONY: hpack

format: stack
	@stack exec -- fourmolu --stdin-input-file $(project_main)
.PHONY: format

ghcid: stack
	@stack exec -- ghcid \
	    --command 'stack repl --ghc-options "-fno-code -fno-break-on-exception -fno-break-on-error -v1 -ferror-spans -j"' \
	    --restart stack.yaml \
	    --restart $(project_name).cabal \
	    --warnings \
	    --outputfile ./ghcid.txt
.PHONY: ghcid

test: stack
	@stack exec -- make -C flame-runtime/testsuite/
	
