default: main

main: 
	sed "s/\'\[/tt[/g" conchask.lhs > conchask.bak.lhs	
	lhs2TeX conchask.lhs -o conchask.tex
	pdflatex conchask.tex

cloudh: 
	sed "s/\'\[/tt[/g" cloudh.lhs > cloudh.bak.lhs
	lhs2TeX cloudh.lhs -o cloudh.tex
	pdflatex cloudh.tex
  
