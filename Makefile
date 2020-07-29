############################################################################
# You can define your own path to COQBIN by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#    COQBIN=/var/tmp/charguer/v8.4/bin/
#
# Note that COQBIN should have a leading slash.
# Note that if you add a settings.sh file, you need to do "make clean" first.

# Default paths for COQBIN, etc are as follows:

COQBIN=

# Use bash as the default shell
SHELL=/bin/bash


#######################################################

COQINCLUDES=-R coq JsCert
COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep
COQFLAGS=

OCAMLBUILD=ocamlbuild
OCAMLBUILDFLAGS=-cflags "-w -20"

#######################################################
# MAIN SOURCE FILES

JS_SRC=\
	coq/JsNumber.v \
	coq/JsSyntax.v \


#######################################################
# MAIN TARGETS

all: coq

.PHONY: all

#######################################################
# Coq Compilation Implicit Rules
%.v.d: %.v
	$(COQDEP) $(COQINCLUDES) $< > $@

# If this rule fails for some reason, try `make clean_all && make`
%.vo: %.v
	$(COQC) $(COQFLAGS) $(COQINCLUDES) $<

#######################################################
# JsAst Specific Rules
.PHONY: coq proof

coq: Makefile.coq
	@$(MAKE) -f Makefile.coq

install: Makefile.coq
	@$(MAKE) -f Makefile.coq install

#######################################################
# CLEAN
.PHONY: clean

clean:
	-rm -f coq/*.{vo,glob,d}

cleanall:
	@$(MAKE) clean
	-rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d .coqdeps.d

##
Makefile.coq: Makefile $(JS_SRC)
	@coq_makefile -f _CoqProject $(JS_SRC) -o Makefile.coq

