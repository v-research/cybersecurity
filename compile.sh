#!/bin/bash
pdflatex v-research_experiment-alpha.tex
biber v-research_experiment-alpha
pdflatex v-research_experiment-alpha.tex
pdflatex v-research_experiment-alpha.tex
