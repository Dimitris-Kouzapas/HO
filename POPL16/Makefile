default: main

main: 
	sed "s/\'\[/tt[/g" cloudh.lhs > cloudh.bak.lhs	
	lhs2TeX cloudh.bak.lhs -o cloudh.tex
	pdflatex cloudh.tex
  
