# ghc and bnfc don't update their output files' timestamps if the contents are
# unchanged, but "make" expects commands to actually produce their output
# files, so this is a poor match.  (By contrast, alex and happy do update their
# output files.)  To defeat that, we touch the output files when trying to make them.

GHC = ghc
# or:
# GHC = cabal exec ghc -- 
INPUT = CTT.hs Connections.hs Eval.hs Main.hs Resolver.hs TypeChecker.hs
GRAMMAR = Exp.cf
GRAMMAR_X_FILES = Exp/Lex.x
GRAMMAR_Y_FILES = Exp/Par.y
GRAMMAR_HS_FILES = Exp/Abs.hs Exp/ErrM.hs Exp/Layout.hs Exp/Print.hs Exp/Skel.hs Exp/Test.hs
GRAMMAR_FILES := $(GRAMMAR_HS_FILES) $(GRAMMAR_X_FILES) $(GRAMMAR_Y_FILES) Exp/Doc.txt
GRAMMAR_HS_FILES += $(GRAMMAR_X_FILES:.x=.hs)
GRAMMAR_HS_FILES += $(GRAMMAR_Y_FILES:.y=.hs)
GRAMMAR_OBJECT_FILES = $(GRAMMAR_HS_FILES:.hs=.o)
GHCOPTIONS = -O2 -rtsopts -v0 -fno-full-laziness -dynamic

all: cubical

# There should be a way to make ghc link with the appropriate libraries,
# without using the --make option, but I can't figure it out.  The libraries
# used are:
#     QuickCheck array bytestring containers deepseq directory filepath haskeline
#     mtl old pretty random template terminfo time transformers unix
# This is what I tried:
#   cubical: $(INPUT:.hs=.o) $(GRAMMAR_OBJECT_FILES); $(GHC) -o $@ $(GHCOPTIONS) $^

cubical: $(INPUT:.hs=.o) $(GRAMMAR_OBJECT_FILES)
	$(GHC) -M -dep-suffix "" $(INPUT) $(GRAMMAR_HS_FILES)
	$(GHC) --make $(GHCOPTIONS) -o cubical Main

build-Makefile: $(INPUT) $(GRAMMAR_HS_FILES)
	$(GHC) -M -dep-suffix "" $^

include Makefile

%.hi %.o: %.hs
	$(GHC) $(GHCOPTIONS) $<
	@ touch $*.hi $*.o
%.hs: %.y
	happy -gca $<
%.hs: %.x
	alex -g $<

bnfc $(GRAMMAR_FILES): Exp.cf
	bnfc --haskell -d Exp.cf
	@ touch $(GRAMMAR_FILES)

TAGS:; hasktags --etags $(INPUT) $(GRAMMAR)

clean:; rm -rf Exp *.log *.aux *.hi *.o cubical TAGS Makefile.bak
git-clean:; git clean -Xdfq
