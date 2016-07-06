CTTFILES := $(shell ls *ctt)

ETAGSOPTS := \
	--language=none \
	--regex='/^\([[:alnum:]]+\) *:/\1/' \
	--regex='/^data +\([[:alnum:]]+\) +=/\1/' \
	--regex='/^module +\([[:alnum:]]+\) +where/\1/'

TAGS: Makefile $(CTTFILES); etags $(ETAGSOPTS) $(CTTFILES)
