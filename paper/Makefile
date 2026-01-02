
NULL =

MODULES = \
  Type \
  Context \
  Permutations \
  Process \
  Congruence \
  Reduction \
  DeadlockFreedom \
  Safety \
  Examples \
  $(NULL)

SOURCES = \
  $(TARGETS) \
  sn-jnl.cls \
  sn-mathphys-num.bst \
  main.bib \
  agda.sty \
  prooftree.sty \
  macros.tex \
  abstract.tex \
  main.tex \
  introduction.tex \
  calculus.tex \
  agda.tex \
  related.tex \
  conclusion.tex \
  $(NULL)

TARGETS = $(MODULES:%=%.tex)

all: $(TARGETS)

archive.zip: $(SOURCES)
	zip $@ $^

%.tex: %.lagda.tex
	agda --latex-dir=. --latex $<

# Context.tex: Type.tex
# Permutations.tex: Context.tex
# Process.tex: Permutations.tex
# Semantics.tex: Process.tex

clean:
	rm -f $(TARGETS)
