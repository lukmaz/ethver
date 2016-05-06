#!/bin/bash

cd src
bnfc -m -haskell ethver.cf
bnfc --latex ethver.cf
pdflatex ethver.tex
cd ..
make
