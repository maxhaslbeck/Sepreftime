# Sepreftime

This repository contains the Isabelle theories accompanying the paper [Refinement with Time -- Refining the Run-Time of Algorithms in Isabelle/HOL](https://drops.dagstuhl.de/opus/volltexte/2019/11075/) by Maximilian P. L. Haslbeck and Peter Lammich.

## Usage

The theories in this repository depend on [Imperative HOL Time](https://github.com/bzhan/Imperative_HOL_Time) which provides a verification environment for Imperative HOL with Time Credits and [NREST](https://github.com/maxhaslbeck/NREST) which provides the `non-deterministic result monad with time`.

The easiest way of making Imperative HOL Time and NREST available is to download it, and add their paths to the local `ROOTS` file (usually in `~/.isabelle/Isabelle2021/ROOTS`).

As for supporting asymptotic notation we need some Analysis background it is advisable to start editing and viewing theories in this repository in the `HOL-Analysis` session (`isabelle jedit -l HOL-Analysis`).

## Further developments

While this repository will not be developed further, it may be updated to coming Isabelle versions.
`Sepreftime` is further developed in [Isabelle-LLVM with Time](https://www21.in.tum.de/~haslbema/llvm-time/), were we extend `NREST` to support multiple currencies and currency refinement.
This repository is maintained by [Maximilian Haslbeck](https://www21.in.tum.de/~haslbema/).
