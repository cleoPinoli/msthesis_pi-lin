
NULL =

SOURCES = \
  2016Goto \
  2019Thiemann \
  2020Castro \
  2020Ciccone \
  2020Rouvet \
  2020Rouvet-lib \
  2020Zalakain \
  2022Jacobs \
  2022Jacobs-lib \
  2023Sano \
  2025Padovani \
  2025Zackon \
  2025Zackon-lib \
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
