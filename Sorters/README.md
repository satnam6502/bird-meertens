# Four sorter cores, related

Claessen, Sheeran and Singh, *The Design and Verification of a Sorter Core*
(CHARME 2001, LNCS 2144), build four sorters for a Virtex-II from Lava
connection patterns. [`Sorters.lean`](Sorters.lean)
copies their definitions and relates the four by calculation.

All four mergers fit one schema, `fly P L`. It places a connection pattern `P`
around the merger of half the size, then adds a last column `L`.

| Merger | `P` | `L` |
|---|---|---|
| `bfly`, Batcher's bitonic merger | `ilv` | `evens` |
| `mergeOE`, Batcher's odd–even merger | `ilv` | `mid ∘ evens` |
| `vfly`, the balanced merger of Dowd et al. | `vee` | `evens` |
| `qfly`, the merger of Canfield and Williamson | `que` | `mid ∘ evens` |

The main results hold for any comparator that keeps lengths and is symmetric,
`f [a, b] = f [b, a]`. The equalities are on lists of length `2ⁿ`.

```
sortB  (n + 1) = two (sortB n)  >-> mergeB  (n + 1)    where mergeB n = parl id reverse >-> bfly n
sortOE (n + 1) = two (sortOE n) >-> mergeOE (n + 1)
qfly n  = unriffle >-> mergeOE n
vfly n  = unriffle >-> mergeB n
sortQ n = hrep n (unriffle >-> mergeOE n)
sortV n = hrep n (unriffle >-> mergeB n)
```

So all four cores come from Batcher's two mergers, used in two ways.

| Merger | Recursive: sort both halves, then merge | Periodic: `n` mergers, each behind `unriffle` |
|---|---|---|
| bitonic, `mergeB` | `sortB` | `sortV` |
| odd–even, `mergeOE` | `sortOE` | `sortQ` |

Canfield and Williamson titled their paper "a sequential sorting network
analogous to the Batcher merger". Here the analogy becomes an equation.
`qfly_eq_unriffle_mergeOE` is one `calc` block; `f` is the comparator.

```
  qfly (n + 2)
= que (qfly (n + 1)) >-> mid (evens f)                                      definition
≈ que (unriffle >-> mergeOE (n + 1)) >-> mid (evens f)                      induction
≈ que unriffle >-> que (mergeOE (n + 1)) >-> mid (evens f)                  que is a functor
≈ ilv unriffle >-> two unriffle >-> two (mergeOE (n + 1)) >-> ilv riffle >-> mid (evens f)
                                                                            ilv riffle undoes ilv unriffle
≈ unriffle >-> unriffle >-> two (mergeOE (n + 1)) >-> ilv riffle >-> mid (evens f)   W3
≈ unriffle >-> unriffle >-> two (mergeOE (n + 1)) >-> riffle >-> mid (evens f)       W4, f symmetric
= unriffle >-> mergeOE (n + 2)                                              definition
```

`vfly_eq_unriffle_mergeB` has the same shape. It uses W5, and the fact that a
butterfly of symmetric components ignores a reversal of its input.

Four wiring laws carry the proofs. Each holds on every list of length `4m`.

| Law | Statement |
|---|---|
| W3 | `ilv unriffle >-> two unriffle = unriffle >-> unriffle` |
| W4 | `ilv riffle = riffle >-> mid (altAux true)` |
| W5 | `alt >-> ilv unriffle >-> ilv (parl id reverse) = unriffle >-> parl id reverse >-> oddsRev` |
| W6 | `ilv (two g) = two (ilv g)` |

They are proved by splitting a list into four interleaved quarter-lists. Then
each wiring only rearranges or reverses the quarters. No position arithmetic is
needed.

Symmetry matters twice. The last column absorbs swaps inside its pairs: that is
the step after W4. And `oddsRev` vanishes into a butterfly. With an asymmetric
component, the `qfly` identity already fails at 4 inputs.

The paper's own lemma from §6, `que (ilv f) = ilv (ilv f)`, follows from W3 and
W6 (`que_ilv`). Its §5 checks are repeated. A kernel proof shows that all four
sorters sort every 4-bit input. Evaluation covers every 8-bit input. The
counterexample `[0, 1, 0, 1]` shows that `bflyCompose` is not a sorter.

## How the identities were found

They were found by testing before they were proved. Two comparator networks are
equal exactly when they agree on every 0–1 input. So exhaustive 0–1 testing
compared candidate equations up to 16 inputs. A symbolic symmetric component
extended the tests to 64 inputs. A search over all 8! input wirings
at 8 inputs showed two families: `{bfly, vfly}` and `{mergeOE, qfly}`. Within a
family, one merger is the other behind a wiring. No wiring links the families.

## Trust

| Theorems | Axioms |
|---|---|
| `qfly_eq_unriffle_mergeOE`, `vfly_eq_unriffle_mergeB`, `sortQ_eq`, `sortV_eq`, `que_ilv` | `propext`, `Classical.choice`, `Quot.sound` |
| `sortB_eq` | `propext`, `Quot.sound` |

## Building

The sorters need only core Lean. Run this from the root of the repository.

```bash
lake build Sorters           # checks the identities, and the paper's §5 checks
```
