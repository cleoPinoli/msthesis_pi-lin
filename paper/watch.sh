#!/bin/sh
exec watchexec -d 500ms -i main.tex agda --latex-dir=. --latex main.lagda.tex
