#!/bin/sh
exec watchexec -d 500ms -f "*.lagda.tex" make
