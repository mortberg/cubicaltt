GHC=ghc
#GHC=cabal exec ghc -- 
INPUT = CTT.hs Connections.hs Eval.hs Main.hs Resolver.hs TypeChecker.hs
GRAMMAR = Exp.cf
GRAMMAR_X_FILES = Exp/Lex.x
GRAMMAR_Y_FILES = Exp/Par.y
GRAMMAR_HS_FILES = Exp/Abs.hs Exp/ErrM.hs Exp/Layout.hs Exp/Print.hs Exp/Skel.hs Exp/Test.hs
GRAMMAR_FILES := $(GRAMMAR_HS_FILES) $(GRAMMAR_X_FILES) $(GRAMMAR_Y_FILES) Exp/Doc.txt
GRAMMAR_HS_FILES += $(GRAMMAR_X_FILES:.x=.hs)
GRAMMAR_HS_FILES += $(GRAMMAR_Y_FILES:.y=.hs)
GRAMMAR_OBJECT_FILES = $(GRAMMAR_HS_FILES:.hs=.o)
GHCOPTIONS = -O2 -rtsopts

all: depends cubical
# this new way doesn't quite work, because it fails to link with the packages
# used: QuickCheck array bytestring containers deepseq directory filepath
# haskeline mtl old pretty random template terminfo time transformers unix
# cubical: $(INPUT:.hs=.o) $(GRAMMAR_OBJECT_FILES); $(GHC) -o $@ $(GHCOPTIONS) $^
# so we do it the old way at the very end
cubical: $(INPUT:.hs=.o) $(GRAMMAR_OBJECT_FILES)
	$(GHC) --make $(OPTIONS) -o cubical -rtsopts Main
depends: $(INPUT) $(GRAMMAR_HS_FILES); $(GHC) -M $^
%.hi %.o: %.hs; $(GHC) $(GHCOPTIONS) $<
%.hs: %.y; happy -gca $<
%.hs: %.x; alex -g $<

$(GRAMMAR_FILES): Exp.cf; bnfc --haskell -d Exp.cf
bnfc:; $(GHC) --make -O$(OPT) Exp/Test.hs -o Exp/Test
clean:; rm -rf Exp *.log *.aux *.hi *.o cubical
git-clean:; git clean -Xdfq

# DO NOT DELETE: Beginning of Haskell dependencies
Exp/ErrM.o : Exp/ErrM.hs
Exp/Abs.o : Exp/Abs.hs
Exp/Skel.o : Exp/Skel.hs
Exp/Skel.o : Exp/ErrM.hi
Exp/Skel.o : Exp/Abs.hi
Exp/Print.o : Exp/Print.hs
Exp/Print.o : Exp/Abs.hi
Exp/Lex.o : Exp/Lex.hs
Exp/Par.o : Exp/Par.hs
Exp/Par.o : Exp/ErrM.hi
Exp/Par.o : Exp/Lex.hi
Exp/Par.o : Exp/Abs.hi
Exp/Layout.o : Exp/Layout.hs
Exp/Layout.o : Exp/Lex.hi
Exp/Test.o : Exp/Test.hs
Exp/Test.o : Exp/ErrM.hi
Exp/Test.o : Exp/Layout.hi
Exp/Test.o : Exp/Abs.hi
Exp/Test.o : Exp/Print.hi
Exp/Test.o : Exp/Skel.hi
Exp/Test.o : Exp/Par.hi
Exp/Test.o : Exp/Lex.hi
Connections.o : Connections.hs
CTT.o : CTT.hs
CTT.o : Connections.hi
Eval.o : Eval.hs
Eval.o : CTT.hi
Eval.o : Connections.hi
Resolver.o : Resolver.hs
Resolver.o : Connections.hi
Resolver.o : Connections.hi
Resolver.o : CTT.hi
Resolver.o : CTT.hi
Resolver.o : Exp/Abs.hi
TypeChecker.o : TypeChecker.hs
TypeChecker.o : Eval.hi
TypeChecker.o : CTT.hi
TypeChecker.o : Connections.hi
Main.o : Main.hs
Main.o : Eval.hi
Main.o : TypeChecker.hi
Main.o : Resolver.hi
Main.o : CTT.hi
Main.o : Exp/ErrM.hi
Main.o : Exp/Layout.hi
Main.o : Exp/Abs.hi
Main.o : Exp/Print.hi
Main.o : Exp/Par.hi
Main.o : Exp/Lex.hi
# DO NOT DELETE: End of Haskell dependencies
