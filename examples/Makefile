CTTFILES := aim.ctt bool.ctt circle.ctt collection.ctt demo.ctt discor.ctt			\
		equiv.ctt ex1.ctt gradLemma.ctt groupoidTrunc.ctt hedberg.ctt hnat.ctt		\
		indSusp.ctt int.ctt integer.ctt interval.ctt list.ctt mult.ctt multS1.ctt	\
		nat.ctt pi.ctt prelude.ctt prop.ctt quotient.ctt retract.ctt sigma.ctt susp.ctt	\
		torus.ctt univalence.ctt

ETAGSOPTS := \
	--language=none \
	--regex='/^\([[:alnum:]]+\) *:/\1/' \
	--regex='/^data +\([[:alnum:]]+\) +=/\1/' \
	--regex='/^module +\([[:alnum:]]+\) +where/\1/'

TAGS: Makefile $(CTTFILES); etags $(ETAGSOPTS) $(CTTFILES)
