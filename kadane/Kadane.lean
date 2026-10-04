/-!
# Kadane's algorithm, derived in the Bird–Meertens formalism

This file replays the maximum segment sum derivation from
R. S. Bird, *Algebraic Identities for Program Calculation*,
The Computer Journal 32(2), 1989, §8. The Wikipedia article on the
Bird–Meertens formalism shows the same derivation as a figure.

The specification is `maxL ∘ map sum ∘ segs`. It is O(n³). Each line of the
`calc` block in `mss_eq_kadane` is a point-free program. Each step is
justified by one named law. The last line is Kadane's O(n) `foldl`.

Every function is over `Int`. The empty segment is a segment, so the answer
is never negative. That lets `0` serve as the unit of `maxL`.
-/

namespace BirdMeertens

open List (map foldl)

/-! ## The vocabulary -/

/-- The largest element, or `0` for the empty list. -/
def maxL : List Int → Int := List.foldr max 0

/-- The sum of a list. -/
def sum : List Int → Int := List.foldr (· + ·) 0

/-- Flatten a list of lists. Bird writes `++/`. -/
def concat : List (List α) → List α := List.flatten

/-- All prefixes, shortest first. -/
def inits : List α → List (List α)
  | [] => [[]]
  | x :: xs => [] :: map (x :: ·) (inits xs)

/-- All suffixes, longest first. -/
def tails : List α → List (List α)
  | [] => [[]]
  | x :: xs => (x :: xs) :: tails xs

/-- All contiguous segments. A segment is a suffix of a prefix. -/
def segs : List α → List (List α) := concat ∘ map tails ∘ inits

/-- Left scan: the list of every intermediate `foldl` accumulator. -/
def scanl (f : β → α → β) : β → List α → List β
  | e, [] => [e]
  | e, x :: xs => e :: scanl f (f e x) xs

/-- Bird's `⊙`: extend the best suffix sum by `b`, never dropping below `0`. -/
def odot (a b : Int) : Int := max (a + b) 0

@[inherit_doc] local infixl:70 " ⊙ " => odot

/-- Bird's `⊗`: carry the running maximum alongside the `⊙` accumulator. -/
def otimes (p : Int × Int) (x : Int) : Int × Int :=
  let w := p.2 ⊙ x
  (max p.1 w, w)

@[inherit_doc] local infixl:70 " ⊗ " => otimes

/-- The specification. Maximum segment sum, O(n³). -/
def mss : List Int → Int := maxL ∘ map sum ∘ segs

/-- Kadane's algorithm. One pass, O(n). -/
def kadane : List Int → Int := Prod.fst ∘ foldl (· ⊗ ·) (0, 0)

/-! ## Facts about `maxL` -/

theorem maxL_nil : maxL [] = 0 := rfl

theorem maxL_cons (a : Int) (l : List Int) : maxL (a :: l) = max a (maxL l) := rfl

theorem maxL_nonneg (l : List Int) : 0 ≤ maxL l := by
  induction l with
  | nil => simp [maxL_nil]
  | cons a l ih => rw [maxL_cons]; omega

theorem maxL_append (l₁ l₂ : List Int) : maxL (l₁ ++ l₂) = max (maxL l₁) (maxL l₂) := by
  induction l₁ with
  | nil => have := maxL_nonneg l₂; simp only [List.nil_append, maxL_nil]; omega
  | cons a l ih => simp only [List.cons_append, maxL_cons, ih]; omega

theorem sum_cons (a : Int) (l : List Int) : sum (a :: l) = a + sum l := rfl

/-- A list's own sum is one of its suffix sums. -/
theorem sum_le_maxL_tails (xs : List Int) : sum xs ≤ maxL (map sum (tails xs)) := by
  cases xs with
  | nil => simp [tails, maxL_cons, sum, maxL_nil]
  | cons x xs => simp only [tails, List.map_cons, maxL_cons]; omega

/-- The seed of a scan is one of its elements. -/
theorem le_maxL_scanl (f : Int → α → Int) (e : Int) (xs : List α) :
    e ≤ maxL (scanl f e xs) := by
  cases xs <;> simp only [scanl, maxL_cons] <;> omega

/-! ## The laws

Each law is stated point-free. Laws that fire in the middle of a pipeline
also carry a trailing `∘ g`, so that `rw` can find them under the
right-associated `∘`. -/

/-- **Map promotion.** `map f ∘ concat = concat ∘ map (map f)`. -/
theorem map_promotion (f : α → β) (g : γ → List (List α)) :
    map f ∘ concat ∘ g = concat ∘ map (map f) ∘ g := by
  funext x; simp [concat, List.map_flatten]

/-- **Fold promotion.** `maxL ∘ concat = maxL ∘ map maxL`. -/
theorem fold_promotion (g : γ → List (List Int)) :
    maxL ∘ concat ∘ g = maxL ∘ map maxL ∘ g := by
  funext x
  simp only [Function.comp_apply, concat]
  induction g x with
  | nil => rfl
  | cons l ls ih => simp only [List.flatten_cons, maxL_append, ih, List.map_cons, maxL_cons]

/-- **Map distributivity.** `map f ∘ map g = map (f ∘ g)`. -/
theorem map_distrib (f : β → γ) (g : α → β) (h : δ → List α) :
    map f ∘ map g ∘ h = map (f ∘ g) ∘ h := by
  funext x; simp

/-- Horner's rule, with an accumulator. -/
theorem horner_acc (a : Int) (ha : 0 ≤ a) (xs : List Int) :
    foldl (· ⊙ ·) a xs = max (a + sum xs) (maxL (map sum (tails xs))) := by
  induction xs generalizing a with
  | nil => simp [tails, sum, maxL_cons, maxL_nil]; omega
  | cons x xs ih =>
    have hs := sum_le_maxL_tails xs
    simp only [List.foldl_cons, tails, List.map_cons, maxL_cons, sum_cons]
    rw [ih _ (by simp only [odot]; omega)]
    simp only [odot]
    omega

/-- **Horner's rule.** `maxL ∘ map sum ∘ tails = foldl (⊙) 0`. -/
theorem horner : maxL ∘ map sum ∘ tails = foldl (· ⊙ ·) 0 := by
  funext xs
  have h0 := maxL_nonneg (map sum (tails xs))
  have hs := sum_le_maxL_tails xs
  simp only [Function.comp_apply, horner_acc 0 (Int.le_refl 0)]
  omega

/-- **Scan lemma.** `map (foldl f e) ∘ inits = scanl f e`. -/
theorem scan_lemma (f : β → α → β) (e : β) :
    map (foldl f e) ∘ inits = scanl f e := by
  funext xs
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih =>
    simp only [Function.comp_apply, inits, List.map_cons, List.foldl_nil, List.map_map,
      scanl] at ih ⊢
    congr 1
    exact ih (f e x)

/-- Fold–scan fusion, with an accumulator. -/
theorem fold_scan_fusion_acc (u v : Int) (hv : v ≤ u) (hu : 0 ≤ u) (xs : List Int) :
    (foldl (· ⊗ ·) (u, v) xs).1 = max u (maxL (scanl (· ⊙ ·) v xs)) := by
  induction xs generalizing u v with
  | nil => simp only [List.foldl_nil, scanl, maxL_cons, maxL_nil]; omega
  | cons x xs ih =>
    have hw := le_maxL_scanl (· ⊙ ·) (v ⊙ x) xs
    have hstep : (u, v) ⊗ x = (max u (v ⊙ x), v ⊙ x) := rfl
    have hnn : 0 ≤ v ⊙ x := by simp only [odot]; omega
    rw [List.foldl_cons, hstep, ih _ _ (by omega) (by omega), scanl, maxL_cons]
    omega

/-- **Fold–scan fusion.** `maxL ∘ scanl (⊙) 0 = fst ∘ foldl (⊗) (0, 0)`. -/
theorem fold_scan_fusion :
    maxL ∘ scanl (· ⊙ ·) 0 = Prod.fst ∘ foldl (· ⊗ ·) (0, 0) := by
  funext xs
  have := maxL_nonneg (scanl (· ⊙ ·) 0 xs)
  simp only [Function.comp_apply, fold_scan_fusion_acc 0 0 (Int.le_refl 0) (Int.le_refl 0)]
  omega

/-! ## The derivation -/

/-- Kadane's algorithm computes the maximum segment sum. Each step names its
law, as in Bird's figure. The cost of each line is on the right. -/
theorem mss_eq_kadane : mss = kadane :=
  calc mss
      = maxL ∘ map sum ∘ segs                                := rfl  -- O(n³)
    _ = maxL ∘ map sum ∘ concat ∘ map tails ∘ inits          := rfl  -- definition of segs
    _ = maxL ∘ concat ∘ map (map sum) ∘ map tails ∘ inits    := by rw [map_promotion]
    _ = maxL ∘ map maxL ∘ map (map sum) ∘ map tails ∘ inits  := by rw [fold_promotion]
    _ = maxL ∘ map (maxL ∘ map sum ∘ tails) ∘ inits          := by rw [map_distrib, map_distrib]; rfl
    _ = maxL ∘ map (foldl (· ⊙ ·) 0) ∘ inits                 := by rw [horner]  -- O(n²)
    _ = maxL ∘ scanl (· ⊙ ·) 0                               := by rw [scan_lemma]  -- O(n)
    _ = Prod.fst ∘ foldl (· ⊗ ·) (0, 0)                      := fold_scan_fusion  -- O(n), one pass
    _ = kadane                                               := rfl

/-! ## Checks -/

-- Bird's example. The best segment is `[4, -1, 2, 1]`.
example : mss [-2, 1, -3, 4, -1, 2, 1, -5, 4] = 6 := by decide +kernel
example : kadane [-2, 1, -3, 4, -1, 2, 1, -5, 4] = 6 := by decide
-- All negative: the empty segment wins.
example : kadane [-3, -1, -2] = 0 := by decide
-- The empty list has only the empty segment. One element is its own best.
example : mss [] = 0 := by decide
example : kadane [] = 0 := by decide
example : mss [5] = 5 := by decide
example : kadane [5] = 5 := by decide

end BirdMeertens
