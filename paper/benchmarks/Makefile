
NULL =

SOURCES = \
  2016Goto \
  2019Thiemann \
  2020Castro \
  2020Zalakain \
  2022Jacobs \
  2023Sano \
  2025Padovani \
  2025Zackon \
  $(NULL)

TARGETS = \
	$(SOURCES:%=%.txt) \
	$(SOURCES:%=%.squeezed.txt) \
	$(NULL)

all: $(TARGETS)

%.zip: %
	zip -r $@ $<

%.txt: %
	cat `find $< -name "*.*"` >$@

%.squeezed.txt: %.txt
	tr -s [:space:] <$< >$@

clean:
	rm -f $(TARGETS)
