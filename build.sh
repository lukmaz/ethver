#!/bin/bash

bnfc -m -haskell ethver.cf
cp MyMakefile Makefile
make
bnfc --latex ethver.cf
pdflatex ethver.tex
