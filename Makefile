awkward_make: SfLib.v Imp.v
	coqc -Q . FSPL SfLib.v; coqc -Q . FSPL Imp.v
clean:
	rm -f *.glob *.log *.vo
