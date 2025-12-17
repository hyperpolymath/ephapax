# SPDX-License-Identifier: EUPL-1.2
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc

VFILES = Syntax.v Typing.v Semantics.v
VOFILES = $(VFILES:.v=.vo)
GLOBFILES = $(VFILES:.v=.glob)

.PHONY: all clean depend doc

all: $(VOFILES)

%.vo: %.v
	$(COQC) $<

depend:
	$(COQDEP) $(VFILES) > .depend

-include .depend

clean:
	rm -f *.vo *.glob *.vok *.vos .depend

doc: $(VOFILES)
	mkdir -p ../docs/coqdoc
	$(COQDOC) --html --toc -d ../docs/coqdoc $(VFILES)
