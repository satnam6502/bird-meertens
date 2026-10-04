# The Bird–Meertens Formalism in Lean 4

[![Build](https://github.com/satnam6502/bird-meertens/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/satnam6502/bird-meertens/actions/workflows/build.yml)

The Bird–Meertens formalism is a way of *calculating* programs, developed by
Richard Bird and Lambert Meertens in the 1980s. You start with a specification
that is obviously correct but often hopelessly inefficient, and then transform
it one step at a time into an efficient program. Every step is an equation
justified by an algebraic law, so the program you end up with is correct by
construction (there is no separate proof to write afterwards, because the
derivation *is* the proof). It is a lot like doing algebra at school, except
that the things being rearranged are programs.

The laws are mostly about lists and the higher order functions that work over
them, like `map`, `foldl`, `foldr` and `scanl`. A typical example is map
fusion, `map f ∘ map g = map (f ∘ g)`, which turns two passes over a list into
one. Others have grander names, like fold promotion, Horner's rule and
fold–scan fusion. Programs are written point-free (as compositions of
functions with no mention of the data flowing through them), which makes them
easy to rewrite with equations. The notation used a lot of squiggly symbols,
which is why the whole approach is affectionately known as *Squiggol*. Good
places to read more are Bird's *An Introduction to the Theory of Lists*
(1987), Meertens' *Algorithmics: Towards Programming as a Mathematical
Activity* (1986), the book *Algebra of Programming* by Bird and de Moor (1997),
and the Wikipedia article on the
[Bird–Meertens formalism](https://en.wikipedia.org/wiki/Bird%E2%80%93Meertens_formalism).

Derivations on paper are lovely to read, but they are also easy to get subtly
wrong. Phrases like "it is easy to see that" can hide a lot, and laws often
have side conditions (an operator must be associative, or have a unit, or
distribute over another) which are easy to forget to check. This repository
replays Bird–Meertens derivations in Lean 4, where every step is a law that
Lean has checked, side conditions and all. A nice bonus is that every line of
a derivation is itself a runnable program, so we can also time each step and
watch the cost drop as the laws are applied.

## Kadane's Algorithm

The first example is Bird's derivation of Kadane's algorithm for the maximum
segment sum problem: find the contiguous segment of a list of integers with
the largest sum. The obvious specification tries every segment and costs
O(n³). Eight lines and seven laws later it has become Kadane's single O(n)
pass over the list, which for lists of 512 elements runs about 110,000 times
faster than the specification. The derivation, the laws, a benchmark that
times every step, and a plot of the running times are all described in
[`kadane/README.md`](kadane/README.md).

## Building

The toolchain is pinned in [`lean-toolchain`](lean-toolchain) and nothing
outside core Lean is needed.

```bash
lake build                   # checks the derivations
lake exe kadane_bench        # times every step of the Kadane derivation
```
