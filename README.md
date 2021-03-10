NOTE
======

This is a fork of a repo containing an implementation of the BCM type system.
Here is how to build the project (branch proj-no-proj !)

```bash
git clean -fx
stack init #choosing a snapshot with the correct dependencies
stack setup #download sandboxed ghc
stack build #building dependencies and executables
```

The rest of this README is old.



CUBICAL
=======

Cubical implements an experimental simple type-checker for type theory
with univalence with an evaluator for closed terms.


INSTALL
-------

To install cubical, a working Haskell and cabal installation are
required.  To build cubical go to the main directory and do

  `cabal install`

To only build (not install) cubical do

  `cabal configure`

  `cabal build`

Alternatively one can also use the Makefile to build the system by
typing:

  `make bnfc && make`

However this requires that the following Haskell packages are
installed:

  mtl, haskeline, directory, BNFC, alex, happy


**Note:** In order to make the mutual keyword work a patched version
of BNFC is needed. To install this download the patched version from

[https://github.com/simhu/bnfc](https://github.com/simhu/bnfc)

and then `cabal install` it.

###Emacs mode:

To install syntax highlighting for cubical files load the cubical.el
file into emacs. In order to load it automatically add

`(load-file "/path/to/cubical.el")`

`(add-to-list 'auto-mode-alist '("\\.cub\\'" . cub-mode))`

to your .emacs file.


USAGE
-----

To run cubical type

  `cubical <filename>`

To enable the debugging mode add the -d flag. In the interaction loop
type :h to get a list of available commands. Note that the current
directory will be taken as the search path for the imports.


OVERVIEW
--------

The program is organized as follows:

 * the files are parsed and produce a list of definitions; the syntax
   is described in the file Exp/Doc.txt or Exp/Doc.tex (auto generated
   by bnfc);

 * this list of definitions is type-checked;

 * if successful, we can then write an expression which is
   type-checked w.r.t. these definitions;

 * if the expression is well-typed it is translated to the cubical
   syntax and evaluated by a "cubical abstract machine", which
   computes its semantics in cubical sets; the result is shown after
   "EVAL:" (to enable the trace of the evaluation run cubical with the
   -d flag);

During type-checking, we consider the primitives listed in
examples/primitive.cub as non interpreted constants. The type-checker
is in the file TypeChecker.hs and is rudimentary (200 lines), without good
error messages.

These primitives however have a meaning in cubical sets, and the
evaluation function computes this meaning. This semantics/evaluation
is described in the file Eval.hs, which is the main file. The most
complex part corresponds to the computations witnessing that the
universe has Kan filling operations.

For writing this semantics, it was convenient to use the alternative
presentation of cubical sets as nominal sets with 01-substitutions
(see A. Pitts' note, references listed below).

The primitives needed to get univalence [are](notes/allprim.txt).


DESCRIPTION OF THE LANGUAGE
---------------------------

We have

 * dependent function types `(x:A) -> B`; non-dependent function types
   can be written as `A -> B`

 * abstraction `\x -> e`

 * named/labelled sum `c1 (x1:A1)...(xn:An) | c2 ... | ...`
   a data type is a recursively defined named sum

 * function defined by case
   `f = split c1 x1 ... xn -> e1 | c2 ... -> ... | ...`

 * sigma types `(x:A) * B`, with the pair constructor (e1,e2)
   and eliminators e.1 and e.2

 * a universe `U` and assume `U:U` for simplicity

 * let/where: `let D in e` where D is a list of definitions an
   alternative syntax is `e where D`

 * `undefined` like in Haskell

 * mutual definitions (this requires a patched version of BNFC, see
   the install instructions above).


The syntax allows Landin's offside rule similar to Haskell.

The basic (untyped) language has a direct simple denotational
semantics. Type theory works with the total part of this language (it
is possible to define totality at the denotational semantics level).
Our evaluator works in a nominal version of this semantics. The
type-checker assumes that we work in this total part, however, there
is no termination check.


DESCRIPTION OF THE SEMANTICS/EVALUATION
---------------------------------------

The values depend on a new class of names, also called directions,
which can be thought of as varying over the unit interval [0,1].  A
path connecting a0 and a1 in the direction x is a value p(x) such that
p(0) = a0 and p(1) = a1.  An element in the identity type a0 = a1 is
then of the form \<x\>p(x) where the name x is bound.  An identity proof
in an identity type will then be interpreted as a "square" of the form
\<x\>\<y\>p(x,y).  See examples/hedberg.cub and the example test3 (in the
current implementation directions/names are represented by numbers).

Operationally, a type is explained by giving what are its Kan filling
operation. For instance, we have to explain what are the Kan filling
for the dependent product.

The main step for interpreting univalence is to transform an
equivalence A -> B to a path in any direction x connecting A and B.
This is a new basic element of the universe, called VEquivEq in the
file Eval.hs which takes a name and arguments A,B,f and the proof that
f is an equivalence. The main part of the work is then to explain the
Kan filling operation for this new type.

The Kan filling for the universe can be seen as a generalization of
the operation of composition of relation.


DESCRIPTION OF THE EXAMPLES
---------------------------

The directory examples contains some examples of proofs. The file
examples/primitive.cub list the new primitives that have cubical set
semantics. These primitive notions imply the axiom of univalence. The
file examples/primitive.cub should be the basis of any development
using univalence.

Most of the example files contain simple test examples of
computations:

 * the file hedberg.cub contains a test computation of a square in
   Nat; the example is test. In the type Nat or Bool, any square
   (proof of identity of two identity proofs) is constant.

 * The file nIso.cub contains a non trivial example of a transport of
   a section of a dependent type along the isomorphism between N and
   N+1; the examples are testSN, testSN1, testSN2, testSN3.

 * The file testInh.cub contains examples of computation for the
   propositional reflection. It gives an example test which produces
   a (surprisingly complex) composition of squares in the universe.

 * The file quotient.cub contains an example of a computation from an
   equivalence class.  The relation R over Nat is to have the same
   parity, and the map is Nat/R -> Bool which returns true if the
   equivalence class contains even number. The examples are test5 and
   test8 which computes the value of this map on the equivalence class
   of five and eight respectively. This uses the file description.cub
   which justifies the axiom of description.

 * The file Kraus.cub contains the example of Nicolai Kraus of the
   myst function, which also shows that we can extract computational
   information from propositions; the example is testMyst zero; the
   computation does not create higher dimensional objects.

 * The file swap.cub contains examples of transport along the
   isomorphism between A x B and B x A; the examples are test14,
   test15.


NEWS (to be detailed)
----

 * Some constants have a direct cubical semantics having better
   behavior w.r.t. equality.  For instance the constant

    `mapOnPath : (A B : U) (f : A -> B) (a b : A)
                 (p : Id A a b) -> Id B (f a) (f b)`

   has a semantics which satisfies the definitional equalities:

    `mapOnPath (id A)       = id A`

    `mapOnPath (g o f)      = (mapOnPath g) o (mapOnPath f)`

    `mapOnPath f (refl A a) = refl B (f a)`

   The evaluation is now used for conversion during type-checking,
   and then we get these equalities definitionally.

   Some proofs are now much simpler than before, e.g. the proof of the
   Graduate Lemma.

 * Similarly we also have eta conversion and surjective pairing.

 * As a test, the particular case of the circle (S1) and the interval
   (I) has been added.


FURTHER WORK (non-exhaustive)
------------

 * The Kan filling operations should be formally proved correct and
   tested on higher inductive types.

 * For higher inductive types, like the circle or the sphere, it would
   be appropriate to *extend* the syntax of type theory, in order to
   get natural elimination rules (see the paper on cubical sets).

 * To explore the termination of the resizing rule.  Computationally
   the resizing rule does not do anything, but the termination seems
   to be an interesting proof-theoretical problem.


REFERENCES AND NOTES
--------------------

 * Voevodsky's home page on univalent foundation

 * HoTT book and webpage:
   [http://homotopytypetheory.org/](http://homotopytypetheory.org/)

 * Type Theory in Color, J.P. Bernardy, G. Moulin

 * A simple type-theoretic language: Mini-TT, Th. Coquand,
   Y. Kinoshita, B. Nordstr�m and M. Takeyama

 * [A cubical set model of type
   theory](http://www.cse.chalmers.se/~coquand/model1.pdf), M. Bezem,
   Th. Coquand and S. Huber.

 * [A remark on contractible family of
   type](http://www.cse.chalmers.se/~coquand/contr.pdf), Th. Coquand.

   This note explains how to derive univalence.

 * [An equivalent presentation of the Bezem-Coquand-Huber category of
   cubical sets](http://arxiv.org/abs/1401.7807), A. Pitts.

   This gives a presentation of the cubical set model in nominal sets.

 * [Remark on singleton
   types](http://www.cse.chalmers.se/~coquand/singl.pdf), Th. Coquand.

 * [Note on Kripke
   model](http://www.cse.chalmers.se/~coquand/countermodel.pdf), M. Bezem
   and Th. Coquand.

 * [Some connections between cubical sets and
   parametricity](http://www.cse.chalmers.se/~coquand/param.pdf),
   Th. Coquand.


AUTHORS
-------

Cyril Cohen, Thierry Coquand, Simon Huber, Anders M�rtberg
