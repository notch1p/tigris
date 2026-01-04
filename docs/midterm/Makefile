#
# This is file `Makefile.sample.pre',
# generated with the docstrip utility.
#
# The original source files were:
#
# ottalt.dtx  (with options: `makefile') 
#
# generated with the docstrip utility.
# Copyright (C) 2011 by Jesse A. Tov
#
# This file may be distributed and/or modified under the
# conditions of the LaTeX Project Public License, either
# version 1.2 of this license or (at your option) any later
# version. The latest version of this license is in:
#
#   http://www.latex-project.org/lppl.txt
#
# and version 1.2 or later is part of all distributions of LaTeX
# version 1999/12/01 or later.
#
#

OTT	     = ott $(OTTFLAGS)
OTTFLAGS	= -signal_parse_errors true \
		  -tex_wrap false -tex_show_meta false

%.ottdump: %.ott
	$(OTT) -picky_multiple_parses true -i $< -writesys $@

%.ott.tex: %.ottdump
	$(OTT) -readsys $< -o $@

%.mng.tex: %.tex %.ottdump
	$(OTT) -readsys $*.ottdump -tex_filter $< $@
	@if grep '<< no parses (' $@ >/dev/null 2>&1 && \
	      [ -z "$(DONTSTOP)" ]; then \
		echo; \
		echo "***** OTT PARSE ERROR(S) *****"; \
		grep -n '<< no parses (' $@; \
		$(RM) $@; \
		exit 1; \
	fi >&2
#
