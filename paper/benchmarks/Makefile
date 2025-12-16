
NULL =

SOURCES = \
  2016Goto \
  2016Goto-safety \
  2016Goto-extra \
  2019Thiemann \
  2020Castro \
  2020Ciccone \
  2020Rouvoet \
  2020Rouvoet-lib \
  2020Zalakain \
  2020Zalakain-lib \
  2022Jacobs \
  2022Jacobs-df \
  2022Jacobs-lib \
  2023Sano \
  2025Zackon \
  2025Zackon-lib \
  2025Padovani \
  2025Padovani-safety \
  2025Padovani-df \
  $(NULL)

TARGETS = \
	$(SOURCES:%=%.stripped.txt) \
	$(SOURCES:%=%.squeezed.txt) \
	$(SOURCES:%=%.size.txt) \
	$(NULL)

all: $(TARGETS)

%.zip: %
	zip -r $@ $<

%.stripped.txt: %
	grep -r -h -v -f $<.patterns $</ >$@

%.squeezed.txt: %.stripped.txt
	tr -s [:space:] <$< >$@

%.size.txt: %.squeezed.txt
	tr -s [:space:] <$< | wc >$@

clean:
	rm -f $(TARGETS)
