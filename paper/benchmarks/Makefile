
NULL =

SOURCES = \
  2016Goto \
  2019Thiemann \
  2019Thiemann-eval \
  2020Castro \
  2020Ciccone \
  2020Rouvet \
  2020Rouvet-lib \
  2020Rouvet-eval \
  2020Zalakain \
  2020Zalakain-lib \
  2022Jacobs \
  2022Jacobs-lib \
  2023Sano \
  2025Zackon \
  2025Zackon-lib \
  2025Padovani \
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

%.size: %
	tr -s [:space:] <$< | wc -c

clean:
	rm -f $(TARGETS)
