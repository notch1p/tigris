BASE     = syntax.ott rules.ott
OTT	     = ott $(OTTFLAGS) 
OTTFLAGS	= -signal_parse_errors true \
		  -tex_wrap false -tex_show_meta false

default: rules.mng.pdf

rules.ottdump: $(BASE)
	$(OTT) $^ -writesys $@

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

rules.mng.pdf: rules.mng.tex rules.ott.tex
	latexmk -pdf $<

.PHONY: clean
clean:
	-latexmk -c rules.tex
	-latexmk -c rules.mng.tex
	-rm rules.mng.pdf *.ottdump *.ott.tex *.mng.tex
