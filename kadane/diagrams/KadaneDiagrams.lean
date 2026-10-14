import LawDiagrams
import Kadane

/-!
# Diagrams of the laws in the Kadane derivation

Each step of `mss_eq_kadane` applies one law. This executable draws one diagram
per step, after the "example instances of used laws" in the Wikipedia article
on the Bird–Meertens formalism. A diagram applies its law to the list
`[3, −4, 2]`, at the point where the derivation uses it. The left path is the
line before the step, the right path the line after it, and both end at the
same value.

Every value is computed by the definitions in `kadane/Kadane.lean`.
`LawDiagrams` lays the diagrams out and checks them. The executable writes
`kadane/diagrams/<law>_light.svg` and `<law>_dark.svg`, where `<law>` is
the name of the law's theorem. Run it from the repository root:

    lake exe kadane_diagrams
-/

namespace KadaneDiagrams

open LawDiagrams
open BirdMeertens
open List (map foldl)

local infixl:70 " ⊙ " => odot
local infixl:70 " ⊗ " => otimes

/-! ## Folds and scans, written out -/

/-- A left fold or scan, written out: a seed, then an operator on each element
in turn. A diagram prints a term and evaluates it, so the value it shows is the
value of the term it shows. -/
inductive Term (α : Type) where
  | seed (a : α)
  | step (t : Term α) (x : Int)
  deriving BEq

/-- The term as text, with `op` for the operator. -/
def Term.text {α : Type} [Draw α] (op : String) : Term α → String
  | .seed a => lineText (Draw.spans a)
  | .step t x =>
    let s := t.text op
    s!"{match t with | .seed _ => s | .step .. => s!"({s})"} {op} {int x}"

/-- The term's value, with `f` for the operator. -/
def Term.eval {α : Type} (f : α → Int → α) : Term α → α
  | .seed a => a
  | .step t x => f (t.eval f) x

/-! ## The laws -/

/-- The example. The best segment is `[3]`. `⊙` drops `3 + −4` to `0`, and
Kadane's pair ends as `(3, 2)`, with two different components. -/
def xs : List Int := [3, -4, 2]

/-- The definition of `segs`, then one diagram per law, in the order of the
`calc` block in `mss_eq_kadane`. -/
def laws : List Law :=
  let pre := inits xs
  let t := map tails pre
  let s := map (map sum) t
  let w := ["a ⊙ b = max (a + b) 0"]
  let fold := foldl .step (Term.seed (0 : Int)) xs
  let folds := map (foldl .step (Term.seed (0 : Int))) pre
  let scan := scanl .step (Term.seed (0 : Int)) xs
  let pairs := foldl .step (Term.seed ((0, 0) : Int × Int)) xs
  [ { file := "segs", name := "Definition of segs",
      statement := "segs = concat ∘ map tails ∘ inits",
      start := node xs,
      before := [("segs", node (segs xs))],
      after := [("inits", node pre), ("map tails", node t), ("concat", node (concat t))],
      arc := true },
    { file := "map_promotion", name := "Map promotion",
      statement := "map f ∘ concat = concat ∘ map (map f)",
      start := node t,
      before := [("concat", node (concat t)), ("map sum", node (map sum (concat t)))],
      after := [("map (map sum)", node s), ("concat", node (concat s))] },
    { file := "fold_promotion", name := "Fold promotion",
      statement := "maxL ∘ concat = maxL ∘ map maxL",
      start := node s,
      before := [("concat", node (concat s)), ("maxL", node (maxL (concat s)))],
      after := [("map maxL", node (map maxL s)), ("maxL", node (maxL (map maxL s)))] },
    { file := "map_distrib", name := "Map distributivity",
      statement := "map f ∘ map g = map (f ∘ g)",
      start := node pre,
      before := [("map tails", node t), ("map (map sum)", node s),
        ("map maxL", node (map maxL s))],
      after := [("map (maxL ∘ map sum ∘ tails)", node (map (maxL ∘ map sum ∘ tails) pre))],
      arc := true },
    { file := "horner", name := "Horner's rule",
      statement := "maxL ∘ map sum ∘ tails = foldl (⊙) 0",
      start := node xs,
      before := [("tails", node (tails xs)), ("map sum", node (map sum (tails xs))),
        ("maxL", node (maxL (map sum (tails xs))))],
      after := [("foldl (⊙) 0", node2 (fold.text "⊙") (fold.eval odot))],
      note := w },
    { file := "scan_lemma", name := "Scan lemma",
      statement := "map (foldl f e) ∘ inits = scanl f e",
      start := node xs,
      before := [("inits", node pre),
        ("map (foldl (⊙) 0)", node2 (folds.map (·.text "⊙")) (folds.map (·.eval odot)))],
      after := [("scanl (⊙) 0", node2 (scan.map (·.text "⊙")) (scan.map (·.eval odot)))],
      note := w },
    { file := "fold_scan_fusion", name := "Fold–scan fusion",
      statement := "maxL ∘ scanl (⊙) 0 = fst ∘ foldl (⊗) (0, 0)",
      start := node xs,
      before := [("scanl (⊙) 0", node (scanl (· ⊙ ·) 0 xs)),
        ("maxL", node (maxL (scanl (· ⊙ ·) 0 xs)))],
      after := [("foldl (⊗) (0, 0)", node2 (pairs.text "⊗") (pairs.eval otimes)),
        ("fst", node (pairs.eval otimes).1)],
      note := w ++ ["(u, v) ⊗ x = (max u w, w), with w = v ⊙ x"] } ]

-- Both paths of the scan lemma build the same terms, before any `⊙` is evaluated.
#guard map (foldl .step (Term.seed (0 : Int))) (inits xs) == scanl .step (Term.seed 0) xs

def main : IO UInt32 := writeAll "kadane_diagrams" "kadane/diagrams" (laws.map fun l => (l.file, l.drawing))

end KadaneDiagrams

def main : IO UInt32 := KadaneDiagrams.main
