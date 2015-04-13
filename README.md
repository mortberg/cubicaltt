Cubical Type Theory
===================

Experimental implementation of a cubical type theory in which the user
can directly manipulate n-dimensional cubes. The language extends type
theory with:

* Path abstraction and application
* Composition and transport
* Isomorphisms can be transformed into equalities
* Some higher inductive types (see "examples/circle.ctt" and
  "examples/susp.ctt")

Because of this it is not necessary to have a special file of
primitives (like in [cubical](https://github.com/simhu/cubical), for
instance function extensionality is provable in the system by:

```
funExt (A : U) (B : A -> U) (f g : (x : A) -> B x)
       (p : (x : A) -> Id (B x) (f x) (g x)) :
       Id ((y : A) -> B y) f g = <i> \(a : A) -> (p a) @ i
```

This proof can be compared with the one in "examples/funext.ctt" which
proves that univalence implies function extensionality (the normal
form of these proofs are almost the same).

For more examples, see "examples/demo.ctt".


Install
-------

To compile the program type:

  `make bnfc && make`

This assumes that the following Haskell packages are installed:

  mtl, haskeline, directory, BNFC, alex, happy


Usage
-----

To run the system type

  `cubical <filename>`

To enable the debugging mode add the -d flag. In the interaction loop
type :h to get a list of available commands. Note that the current
directory will be taken as the search path for the imports.


References and notes
--------------------

 * [A Cubical Type
   Theory](http://www.cse.chalmers.se/~coquand/rules5.pdf) -
   The typing rules of the system

 * Voevodsky's page on [univalent
   foundations](http://www.math.ias.edu/~vladimir/Site3/Univalent_Foundations.html)

 * HoTT book and webpage:
   [http://homotopytypetheory.org/](http://homotopytypetheory.org/)

 * [A Cubical Approach to Synthetic Homotopy
   Theory][http://dlicata.web.wesleyan.edu/pubs/lb15cubicalsynth/lb15cubicalsynth.pdf),
   Dan Licata, Guillaume Brunerie.

 * [Type Theory in
   Color](http://www.cse.chalmers.se/~bernardy/CCCC.pdf),
   Jean-Philippe Bernardy, Guilhem Moulin.

 * [A simple type-theoretic language:
   Mini-TT](http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf),
   Thierry Coquand, Yoshiki Kinoshita, Bengt Nordström and Makoto
   Takeyama - This presents the type theory that the system is based
   on.

 * [A cubical set model of type
   theory](http://www.cse.chalmers.se/~coquand/model1.pdf), Marc
   Bezem, Thierry Coquand and Simon Huber.

 * [An equivalent presentation of the Bezem-Coquand-Huber category of
   cubical sets](http://arxiv.org/abs/1401.7807), Andrew Pitts - This
   gives a presentation of the cubical set model in nominal sets.

 * [Remark on singleton
   types](http://www.cse.chalmers.se/~coquand/singl.pdf), Thierry
   Coquand.

 * [Note on Kripke
   model](http://www.cse.chalmers.se/~coquand/countermodel.pdf), Marc
   Bezem and Thierry Coquand.


Authors
-------

Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg
