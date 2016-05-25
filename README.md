# AutoCorres examples

[AutoCorres][] is a tool which can automatically produce a monadic abstraction
of a C program, together with an [Isabelle/HOL][Isabelle] proof of
correspondence between the abstraction and a [low-level embedding][c-parser] of
the C program. AutoCorres was developed primarily by [David Greenaway][] during
his [PhD][] at [NICTA][] and [UNSW][].

[AutoCorres]: http://ssrg.nicta.com.au/projects/TS/autocorres/
[Isabelle]: http://isabelle.in.tum.de/
[c-parser]: http://ssrg.nicta.com.au/software/TS/c-parser/
[David Greenaway]: http://www.davidgreenaway.com/
[PhD]: http://ssrg.nicta.com.au/publications/nictaabstracts/8758.pdf
[NICTA]: https://www.nicta.com.au/
[UNSW]: https://www.cse.unsw.edu.au/

AutoCorres is currently distributed in the [tools][] directory of the [l4v][]
verifcation of the [seL4][] microkernel.

[tools]: https://github.com/seL4/l4v/tree/master/tools
[l4v]: https://github.com/seL4/l4v
[seL4]: http://sel4.systems/

This repository contains a couple of example proofs using AutoCorres, which I
reworked for my own educational purposes.

