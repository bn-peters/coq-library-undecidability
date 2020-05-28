# Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory

Yannick Forster <forster@ps.uni-saarland>, Dominik Kirst <kirst@ps.uni-saarland.de>, Dominik Wehr <s8dowehr@stud.uni-saarland.de>

This is the Coq formalisation of the paper ["Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory"](https://www.ps.uni-saarland.de/extras/fol-undec/).

## How to compile the code

You need to install the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability/) and use Coq 8.11. This is easiest via `opam`:

``` shell
opam switch create fol-completeness 4.09.1+flambda
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add psl-opam-repository https://github.com/uds-psl/psl-opam-repository.git
opam update
opam install coq-library-undecidability.0.1~alpha+8.11
```

You can also install the library manually by installing the dependencies and then issuing `make install` in the library directory.

Afterwards, you can simply type `make` in this directory.
