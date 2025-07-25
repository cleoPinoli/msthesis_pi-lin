#!/bin/sh
exec watchexec -d 500ms -i formalization.tex agda --latex-dir=. --latex formalization.lagda.tex
