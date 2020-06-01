#!/bin/bash
latexOutputDir="latex-output-dir"
latexInputFile="main.tex"
pdfOutputDir="${latexOutputDir}/${latexInputFile%.*}.pdf"

if [[ ! -d $latexOutputDir ]]; then 
	mkdir $latexOutputDir
fi

if pdflatex -halt-on-error -output-directory=$latexOutputDir $latexInputFile
then 
	if [ "$1" != "-short" ] && [ "$1" != "-s" ] 
	then 
		if biber --nodieonerror --input-directory=$latexOutputDir --output-directory=$latexOutputDir ${latexInputFile%.*}  
		then
			if pdflatex -halt-on-error -output-directory=$latexOutputDir $latexInputFile
			then 
				pdflatex -halt-on-error -output-directory=$latexOutputDir $latexInputFile 
			fi
		fi
	fi

	if [[ -f $pdfOutputDir ]]
	then
		mv $pdfOutputDir `dirname $0`
	fi
fi
