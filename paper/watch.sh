#!/bin/sh
exec watchexec -d 500ms -e .lagda.tex agda --latex-dir=. --latex formalization.lagda.tex
