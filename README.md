LambdaJS
========

LambdaJS is small, tested, reduction semantics for JavaScript. For a quick 
introduction, see our blog post:

  http://brownplt.github.com/2011/09/29/js-essence.html

For a more technical introduction, see our ECOOP 2010 paper on LambdaJS:

  http://www.cs.brown.edu/~sk/Publications/Papers/Published/gsk-essence-javascript/


- coq/ contains our mechanized semantics in Coq. Tested with Coq 8.3 and 8.4
  beta.

- Redex/ contains our mechanized semantics in PLT Redex.  Tested with 
  Racket 5.2.

- haskell/ contains an implementation of desugaring.  Tested with GHC 7.0.4.
  This software uses packages available on Hackage.

- DisableXHR/ contains an implementation of our safe-subset example.  Tested
  with GHC 6.10.4.  This tool requires the LambdaJS Haskell package to be built
  and installed first.

Semantics for ECMAScript 5
==========================

LambdaJS roughly models ECMAScript 3. The latest version of JavaScript, ECMAScript 5, is considerably more complex, so we decided to develop it from scratch.
The following blog post describes S5, our semantics for ES5:

  http://brownplt.github.com/2011/11/11/s5-javascript-semantics.html

The code for S5 is also available:

  https://github.com/brownplt/LambdaS5
