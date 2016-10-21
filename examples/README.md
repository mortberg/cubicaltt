Cubical Type Theory: examples
=============================

This folder contains a lot of examples implemented using
cubicaltt. The files contain:

* binnat.ctt - Binary natural numbers and isomorphism to unary
               numbers. Example of data and program refinement by
               doing a proof for unary numbers by computation with
               binary numbers.

bool.ctt - Booleans. Proof that bool = bool by negation and various
           other simple examples.

category.ctt - Categories. Structure identity principle. Pullbacks.

circle.ctt - The circle as a HIT. Computation of winding numbers.

collection.ctt - This file proves that the collection of all
                 sets is a groupoid.

csystem.ctt - Definition of C-systems and universe
              categories. Construction of a C-system from a universe
              category.

demo.ctt - Demo of the system.

discor.ctt - or A B is discrete if A and B are.

equiv.ctt - Definition of equivalences and various results on these,
            including the "graduate lemma".

groupoidTrunc.ctt - The groupoid truncation as a HIT.

hedberg.ctt - Hedbergs lemma: a type with decidable equality is a set.

helix.ctt - The loop space of the circle is equal to Z.

hnat.ctt - Non-standard natural numbers as a HIT without any path
           constructor.

hz.ctt - Z defined as a (impredicative set) quotient of nat * nat
 
idtypes.ctt - Identity types (variation of Path types with
              definitional equality for J). Including a proof
              univalence expressed only using Id.

injective.ctt - Two definitions of injectivity and proof that they are
                equal.

int.ctt - The integers as nat + nat with proof that suc is an iso
          giving a non-trivial path from Z to Z.

integer.ctt - The integers as a HIT (identifying +0 with -0). Proof
              that this representation is isomorphic to the one in
              int.ctt

interval.ctt - The interval as a HIT. Proof of function extensionality
               from it.

list.ctt - Lists. Various basic lemmas in "cubical style".

nat.ctt - Natural numbers. Various basic lemmas in "cubical style".

ordinal.ctt - Ordinals.

pi.ctt - Characterization of equality in pi types.

prelude.ctt - The prelude. Definition of Path types and basic
              operations on them (refl, mapOnPath,
              funExt...). Definition of prop, set and groupoid. Some
              basic data types (empty, unit, or, and).

propTrunc.ctt - Propositional truncation as a HIT. (WARNING: not
                working correctly)

retract.ctt - Definition of retract and section.

setquot.ctt - Formalization of impredicative set quotients á la
              Voevodsky.

sigma.ctt - Various results about sigma types.

subset.ctt - Two definitions of a subset and a proof that they are
             equal.

summary.ctt - Summary of where to find the results and examples from
              the cubical type theory paper.

susp.ctt - Suspension. Definition of the circle as the suspension of
           bool and a proof that this is equal to the standard HIT
           representation of the circle.

torsor.ctt - Torsors. Proof that S1 is equal to BZ, the classifying
             space of Z.

torus.ctt - Proof that Torus = S1 * S1.

univalence.ctt - Proofs of the univalence axiom. 
