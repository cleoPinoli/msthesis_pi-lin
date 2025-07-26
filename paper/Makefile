
NULL =

MODULES = \
  Type \
  Context \
  Permutations \
  Process \
  Semantics \
  $(NULL)

TARGETS = $(MODULES:%=%.tex)

all: $(TARGETS)

%.tex: %.lagda.tex
	agda --latex-dir=. --latex $<

# Context.tex: Type.tex
# Permutations.tex: Context.tex
# Process.tex: Permutations.tex
# Semantics.tex: Process.tex

clean:
	rm -f $(TARGETS)
