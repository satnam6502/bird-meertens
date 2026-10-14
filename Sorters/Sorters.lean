/-!
# Four sorter cores, related by calculation

K. Claessen, M. Sheeran and S. Singh, *The Design and Verification of a Sorter
Core*, CHARME 2001, LNCS 2144, pp. 355–368, builds four sorters for a Xilinx
Virtex-II from a few connection patterns:

* `sortB`, Batcher's bitonic sorter, recursive;
* `sortOE`, Batcher's odd–even merge sorter, recursive;
* `sortV`, periodic: `n` copies of Dowd et al.'s balanced merger `vfly`;
* `sortQ`, periodic: `n` copies of Canfield and Williamson's merger `qfly`.

The definitions below follow the paper's Lava code. This file then relates the
four by calculation:

* all four mergers are one schema, `fly P L`: a connection pattern `P` around a
  smaller merger, then a last column `L`;
* `sortB` has the same shape as `sortOE`, once its merger is read as a merger
  of two sorted halves, `mergeB`;
* the periodic mergers are the recursive ones behind a wiring:
  `qfly n = unriffle >-> mergeOE n` and `vfly n = unriffle >-> mergeB n`.

So all four sorter cores come from Batcher's two mergers. The two recursive ones
merge sorted halves; the two periodic ones run one merger `n` times, behind an
`unriffle`.

The paper's own lemma `que (ilv f) = ilv (ilv f)` falls out of the same wiring
laws (`que_ilv`). Its fixed-size checks are repeated at the end of the file.

Circuits are functions on lists. A sorter on `2ⁿ` inputs only has to behave on
lists of that length, so most laws are equalities `f ≈[N] g` on lists of length
`N`. The comparator is a parameter. The laws need only that it keeps lengths
and is symmetric, `f [a, b] = f [b, a]`.
-/

namespace BirdMeertens.Sorters

/-! ## Circuits and connection patterns -/

/-- A circuit maps a list of wires to a list of wires. -/
abbrev Circuit (α : Type) := List α → List α

/-- Serial composition, left to right: Lava's `>->`. -/
def seq (f g : Circuit α) : Circuit α := fun xs => g (f xs)

@[inherit_doc] infixl:60 " >-> " => seq

/-- `parl f g` applies `f` to the first half and `g` to the second. -/
def parl (f g : Circuit α) : Circuit α := fun xs =>
  f (xs.take (xs.length / 2)) ++ g (xs.drop (xs.length / 2))

/-- Two copies of `f`, one on each half. -/
def two (f : Circuit α) : Circuit α := parl f f

/-- The wires at even positions. -/
def evensIdx : List α → List α
  | a :: _ :: cs => a :: evensIdx cs
  | l => l

/-- The wires at odd positions. -/
def oddsIdx : List α → List α
  | _ :: b :: cs => b :: oddsIdx cs
  | _ => []

/-- Unshuffle: the even positions, then the odd ones. -/
def unriffle (xs : List α) : List α := evensIdx xs ++ oddsIdx xs

/-- Two lists, alternately. -/
def interleave : List α → List α → List α
  | a :: as, b :: bs => a :: b :: interleave as bs
  | as, [] => as
  | [], bs => bs

/-- The perfect shuffle: halve the pack, then interleave the halves. -/
def riffle (xs : List α) : List α :=
  interleave (xs.take (xs.length / 2)) (xs.drop (xs.length / 2))

/-- `ilv f` applies `f` to the even positions and to the odd positions. -/
def ilv (f : Circuit α) : Circuit α := unriffle >-> two f >-> riffle

/-- `evens f` applies `f` to each adjacent pair. -/
def evens (f : Circuit α) : Circuit α
  | a :: b :: cs => f [a, b] ++ evens f cs
  | l => l

/-- `mid f` passes the first and last wires through and applies `f` to the rest. -/
def mid (f : Circuit α) : Circuit α := fun xs =>
  if xs.length < 2 then xs
  else xs.take 1 ++ f ((xs.drop 1).take (xs.length - 2)) ++ xs.drop (xs.length - 1)

/-- Swap every other pair, starting with a swap when `s` is set. -/
def altAux : Bool → Circuit α
  | s, a :: b :: cs => (if s then [b, a] else [a, b]) ++ altAux (!s) cs
  | _, l => l

/-- `alt` swaps every second pair: `[1, 2, 4, 3, 5, 6, 8, 7, …]`. -/
def alt : Circuit α := altAux false

/-- The balanced merger's pattern: `ilv` between two `alt`s. -/
def vee (f : Circuit α) : Circuit α := alt >-> ilv f >-> alt

/-- Canfield and Williamson's pattern: `two`, between interleaved shuffles. -/
def que (f : Circuit α) : Circuit α := ilv unriffle >-> two f >-> ilv riffle

/-- `k` copies of `f` in series. -/
def hrep : Nat → Circuit α → Circuit α
  | 0, _ => id
  | k + 1, f => f >-> hrep k f

/-! ## The mergers and sorters of the paper -/

/-- Batcher's bitonic merger: a butterfly on `2ⁿ` inputs. -/
def bfly : Nat → Circuit α → Circuit α
  | 0, _ => id
  | 1, f => f
  | n + 2, f => ilv (bfly (n + 1) f) >-> evens f

/-- Batcher's odd–even merger. Only the last column differs from `bfly`. -/
def mergeOE : Nat → Circuit α → Circuit α
  | 0, _ => id
  | 1, cmp => cmp
  | n + 2, cmp => ilv (mergeOE (n + 1) cmp) >-> mid (evens cmp)

/-- Dowd et al.'s balanced merger. -/
def vfly : Nat → Circuit α → Circuit α
  | 0, _ => id
  | 1, f => f
  | n + 2, f => vee (vfly (n + 1) f) >-> evens f

/-- Canfield and Williamson's merger. -/
def qfly : Nat → Circuit α → Circuit α
  | 0, _ => id
  | 1, f => f
  | n + 2, f => que (qfly (n + 1) f) >-> mid (evens f)

/-- Batcher's bitonic sorter. -/
def sortB : Nat → Circuit α → Circuit α
  | 0, _ => id
  | n + 1, cmp => parl (sortB n cmp) (sortB n cmp >-> List.reverse) >-> bfly (n + 1) cmp

/-- Batcher's odd–even merge sorter. -/
def sortOE : Nat → Circuit α → Circuit α
  | 0, _ => id
  | n + 1, cmp => two (sortOE n cmp) >-> mergeOE (n + 1) cmp

/-- A periodic sorter: `n` balanced mergers in series. -/
def sortV (n : Nat) (cmp : Circuit α) : Circuit α := hrep n (vfly n cmp)

/-- A periodic sorter: `n` Canfield–Williamson mergers in series. -/
def sortQ (n : Nat) (cmp : Circuit α) : Circuit α := hrep n (qfly n cmp)

/-- `n` bitonic mergers in series. The paper shows this is not a sorter. -/
def bflyCompose (n : Nat) (cmp : Circuit α) : Circuit α := hrep n (bfly n cmp)

/-- The two-sorter on bits: one AND gate and one OR gate. -/
def twoBitSort : Circuit Bool
  | [a, b] => [a && b, a || b]
  | l => l

/-! ## What the laws assume -/

/-- `f` keeps the number of wires. -/
abbrev LP (f : Circuit α) : Prop := ∀ xs, (f xs).length = xs.length

/-- A two-input component that does not care which input is which. -/
def Symm (f : Circuit α) : Prop := ∀ a b, f [a, b] = f [b, a]

/-- `f` and `g` agree on lists of length `N`. -/
def EqOn (N : Nat) (f g : Circuit α) : Prop := ∀ xs : List α, xs.length = N → f xs = g xs

@[inherit_doc] notation:50 f " ≈[" N "] " g:50 => EqOn N f g

instance : Trans (EqOn (α := α) N) (EqOn N) (EqOn N) where
  trans h₁ h₂ xs hx := (h₁ xs hx).trans (h₂ xs hx)

theorem EqOn.of_eq {f g : Circuit α} (h : f = g) : f ≈[N] g := fun _ _ => h ▸ rfl

/-! ## Lengths -/

@[simp] theorem seq_apply (f g : Circuit α) (xs : List α) : (f >-> g) xs = g (f xs) := rfl

@[simp] theorem length_evensIdx : ∀ xs : List α, (evensIdx xs).length = (xs.length + 1) / 2
  | [] => by simp [evensIdx]
  | [_] => by simp [evensIdx]
  | _ :: _ :: cs => by simp only [evensIdx, List.length_cons, length_evensIdx cs]; omega

@[simp] theorem length_oddsIdx : ∀ xs : List α, (oddsIdx xs).length = xs.length / 2
  | [] => by simp [oddsIdx]
  | [_] => by simp [oddsIdx]
  | _ :: _ :: cs => by simp only [oddsIdx, List.length_cons, length_oddsIdx cs]; omega

@[simp] theorem length_unriffle (xs : List α) : (unriffle xs).length = xs.length := by
  simp only [unriffle, List.length_append, length_evensIdx, length_oddsIdx]; omega

@[simp] theorem length_interleave : ∀ as bs : List α,
    (interleave as bs).length = as.length + bs.length
  | _ :: as, _ :: bs => by simp only [interleave, List.length_cons, length_interleave as bs]; omega
  | [], [] => rfl
  | _ :: _, [] => by simp [interleave]
  | [], _ :: _ => by simp [interleave]

@[simp] theorem length_riffle (xs : List α) : (riffle xs).length = xs.length := by
  simp only [riffle, length_interleave, List.length_take, List.length_drop]; omega

theorem LP.parl {f g : Circuit α} (hf : LP f) (hg : LP g) : LP (parl f g) := by
  intro xs
  simp only [Sorters.parl, List.length_append, hf _, hg _, List.length_take, List.length_drop]
  omega

theorem LP.two {f : Circuit α} (hf : LP f) : LP (two f) := hf.parl hf

theorem LP.seq {f g : Circuit α} (hf : LP f) (hg : LP g) : LP (f >-> g) := by
  intro xs; rw [seq_apply, hg, hf]

theorem LP.id : LP (id : Circuit α) := fun _ => rfl

theorem LP.reverse : LP (List.reverse : Circuit α) := fun _ => List.length_reverse

theorem LP.unriffle : LP (unriffle : Circuit α) := length_unriffle

theorem LP.riffle : LP (riffle : Circuit α) := length_riffle

theorem LP.ilv {f : Circuit α} (hf : LP f) : LP (ilv f) :=
  (LP.unriffle.seq hf.two).seq LP.riffle

theorem LP.evens {f : Circuit α} (hf : LP f) : LP (evens f)
  | [] => rfl
  | [_] => rfl
  | a :: b :: cs => by
    simp only [Sorters.evens, List.length_append, hf _, List.length_cons, List.length_nil,
      LP.evens hf cs]
    omega

theorem LP.mid {f : Circuit α} (hf : LP f) : LP (mid f) := by
  intro xs
  unfold Sorters.mid
  split
  · rfl
  · simp only [List.length_append, hf _, List.length_take, List.length_drop]; omega

theorem LP.altAux : ∀ (s : Bool), LP (altAux s : Circuit α)
  | _, [] => rfl
  | _, [_] => rfl
  | s, a :: b :: cs => by
    cases s <;> simp only [Sorters.altAux, List.length_append, LP.altAux _ cs] <;> simp <;> omega

theorem LP.alt : LP (alt : Circuit α) := LP.altAux false

theorem LP.hrep {f : Circuit α} (hf : LP f) : ∀ k, LP (hrep k f)
  | 0 => LP.id
  | k + 1 => hf.seq (LP.hrep hf k)

theorem LP.bfly {f : Circuit α} (hf : LP f) : ∀ n, LP (bfly n f)
  | 0 => LP.id
  | 1 => hf
  | n + 2 => (LP.bfly hf (n + 1)).ilv.seq hf.evens

theorem LP.mergeOE {f : Circuit α} (hf : LP f) : ∀ n, LP (mergeOE n f)
  | 0 => LP.id
  | 1 => hf
  | n + 2 => (LP.mergeOE hf (n + 1)).ilv.seq hf.evens.mid

/-! ## Wires by position

Each wiring is described by where output `i` comes from. A law about wirings
then reduces to arithmetic on positions. -/

theorem getElem?_evensIdx : ∀ (xs : List α) (i : Nat), (evensIdx xs)[i]? = xs[2 * i]?
  | [], _ => by simp [evensIdx]
  | [_], i => by cases i <;> simp [evensIdx] <;> omega
  | _ :: _ :: _, 0 => by simp [evensIdx]
  | _ :: _ :: cs, i + 1 => by
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    simp [evensIdx, getElem?_evensIdx cs i]

theorem getElem?_oddsIdx : ∀ (xs : List α) (i : Nat), (oddsIdx xs)[i]? = xs[2 * i + 1]?
  | [], _ => by simp [oddsIdx]
  | [_], i => by cases i <;> simp [oddsIdx] <;> omega
  | _ :: _ :: _, 0 => by simp [oddsIdx]
  | _ :: _ :: cs, i + 1 => by
    rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega]
    simp [oddsIdx, getElem?_oddsIdx cs i]

theorem getElem?_unriffle (xs : List α) (i : Nat) :
    (unriffle xs)[i]? = if i < (xs.length + 1) / 2 then xs[2 * i]?
      else xs[2 * (i - (xs.length + 1) / 2) + 1]? := by
  unfold unriffle
  split
  · rw [List.getElem?_append_left (by simp; omega), getElem?_evensIdx]
  · rw [List.getElem?_append_right (by simp; omega), getElem?_oddsIdx, length_evensIdx]

/-- Close a goal about positions: equal indices, an index past the end, or
contradictory hypotheses. -/
macro "close_idx" : tactic => `(tactic| first
  | rfl
  | (congr 1; omega)
  | (simp only [List.getElem?_eq_none_iff]; omega)
  | (apply Eq.symm; simp only [List.getElem?_eq_none_iff]; omega)
  | (exfalso; omega))

/-- `interleave as bs`, position by position, when `bs` has the same length as `as`
or one more. -/
theorem getElem?_interleave : ∀ (as bs : List α), as.length ≤ bs.length →
    bs.length ≤ as.length + 1 → ∀ i, (interleave as bs)[i]? =
      if i / 2 < as.length then (if i % 2 = 0 then as[i / 2]? else bs[i / 2]?)
      else (if i % 2 = 0 then bs[i / 2]? else none)
  | [], [], _, _, i => by simp [interleave]
  | [], [_], _, _, i => by
    rcases i with _ | _ | i <;> simp [interleave] <;> omega
  | [], _ :: _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _, _ => absurd h (by simp)
  | _ :: _, _ :: _, _, _, 0 => by simp [interleave]
  | _ :: _, _ :: _, _, _, 1 => by simp [interleave]
  | _ :: as, _ :: bs, h₁, h₂, i + 2 => by
    simp only [interleave, List.getElem?_cons_succ]
    rw [getElem?_interleave as bs (by simpa using h₁) (by simpa using h₂) i,
      show (i + 2) / 2 = i / 2 + 1 by omega, show (i + 2) % 2 = i % 2 by omega]
    simp

/-- `riffle xs`, position by position: even positions come from the first half,
odd ones from the second. -/
theorem getElem?_riffle (xs : List α) (i : Nat) :
    (riffle xs)[i]? = if i / 2 < xs.length / 2 then
        (if i % 2 = 0 then xs[i / 2]? else xs[xs.length / 2 + i / 2]?)
      else (if i % 2 = 0 then xs[xs.length / 2 + i / 2]? else none) := by
  unfold riffle
  rw [getElem?_interleave _ _ (by simp; omega) (by simp; omega)]
  simp only [List.length_take, List.getElem?_take, List.getElem?_drop]
  repeat' split
  all_goals first | rfl | omega

theorem getElem?_parl (f g : Circuit α) (hf : LP f) (xs : List α) (i : Nat) :
    (parl f g xs)[i]? = if i < xs.length / 2 then (f (xs.take (xs.length / 2)))[i]?
      else (g (xs.drop (xs.length / 2)))[i - xs.length / 2]? := by
  unfold parl
  split
  · rw [List.getElem?_append_left (by rw [hf]; simp; omega)]
  · rw [List.getElem?_append_right (by rw [hf]; simp; omega), hf]
    simp only [List.length_take]
    congr 2
    omega

/-- Lists of length `N` are equal if they agree at every position below `N`. -/
theorem ext_getElem?_of_length {l₁ l₂ : List α} (h₁ : l₁.length = N) (h₂ : l₂.length = N)
    (h : ∀ i < N, l₁[i]? = l₂[i]?) : l₁ = l₂ :=
  List.ext_getElem? fun i => if hi : i < N then h i hi else by
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ## Laws of the wirings -/

theorem riffle_unriffle (xs : List α) (h : xs.length % 2 = 0) : riffle (unriffle xs) = xs := by
  apply ext_getElem?_of_length (N := xs.length) (by simp) rfl
  intro i hi
  simp only [getElem?_riffle, length_unriffle, getElem?_unriffle]
  repeat' split
  all_goals close_idx

theorem unriffle_riffle (xs : List α) (h : xs.length % 2 = 0) : unriffle (riffle xs) = xs := by
  apply ext_getElem?_of_length (N := xs.length) (by simp) rfl
  intro i hi
  simp only [getElem?_unriffle, length_riffle, getElem?_riffle]
  repeat' split
  all_goals close_idx

/-! ## The algebra of interleavings

Lists are taken apart into interleaved pieces. The wiring laws then follow by
rewriting, with no positions in sight. -/

theorem interleave_evensIdx_oddsIdx : ∀ xs : List α, xs.length % 2 = 0 →
    interleave (evensIdx xs) (oddsIdx xs) = xs
  | [], _ => rfl
  | [_], h => absurd h (by simp)
  | a :: b :: cs, h => by
    simp only [evensIdx, oddsIdx, interleave]
    rw [interleave_evensIdx_oddsIdx cs (by simp at h; omega)]

theorem evensIdx_interleave : ∀ as bs : List α, as.length = bs.length →
    evensIdx (interleave as bs) = as
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [interleave, evensIdx]; rw [evensIdx_interleave as bs (by simpa using h)]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

theorem oddsIdx_interleave : ∀ as bs : List α, as.length = bs.length →
    oddsIdx (interleave as bs) = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [interleave, oddsIdx]; rw [oddsIdx_interleave as bs (by simpa using h)]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

theorem unriffle_interleave (as bs : List α) (h : as.length = bs.length) :
    unriffle (interleave as bs) = as ++ bs := by
  rw [unriffle, evensIdx_interleave as bs h, oddsIdx_interleave as bs h]

theorem riffle_append (as bs : List α) (h : as.length = bs.length) :
    riffle (as ++ bs) = interleave as bs := by
  have : (as ++ bs).length / 2 = as.length := by simp; omega
  rw [riffle, this, List.take_left', List.drop_left'] <;> rfl

theorem interleave_append : ∀ (as bs cs ds : List α), as.length = bs.length →
    interleave (as ++ cs) (bs ++ ds) = interleave as bs ++ interleave cs ds
  | [], [], _, _, _ => rfl
  | a :: as, b :: bs, cs, ds, h => by
    simp only [List.cons_append, interleave]
    rw [interleave_append as bs cs ds (by simpa using h)]
  | [], _ :: _, _, _, h => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)

theorem parl_append (f g : Circuit α) (as bs : List α) (h : as.length = bs.length) :
    parl f g (as ++ bs) = f as ++ g bs := by
  have : (as ++ bs).length / 2 = as.length := by simp; omega
  rw [parl, this, List.take_left', List.drop_left'] <;> rfl

theorem two_append (f : Circuit α) (as bs : List α) (h : as.length = bs.length) :
    two f (as ++ bs) = f as ++ f bs := parl_append f f as bs h

theorem evensIdx_append : ∀ as bs : List α, as.length % 2 = 0 →
    evensIdx (as ++ bs) = evensIdx as ++ evensIdx bs
  | [], _, _ => rfl
  | [_], _, h => absurd h (by simp)
  | a :: b :: as, bs, h => by
    simp only [List.cons_append, evensIdx]
    rw [evensIdx_append as bs (by simp at h; omega)]

theorem oddsIdx_append : ∀ as bs : List α, as.length % 2 = 0 →
    oddsIdx (as ++ bs) = oddsIdx as ++ oddsIdx bs
  | [], _, _ => rfl
  | [_], _, h => absurd h (by simp)
  | a :: b :: as, bs, h => by
    simp only [List.cons_append, oddsIdx]
    rw [oddsIdx_append as bs (by simp at h; omega)]

theorem reverse_interleave : ∀ as bs : List α, as.length = bs.length →
    (interleave as bs).reverse = interleave bs.reverse as.reverse
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    have h' : as.length = bs.length := by simpa using h
    simp only [interleave, List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [reverse_interleave as bs h', interleave_append _ _ _ _ (by simp [h'])]
    rfl
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

/-- Four equal-length lists, interleaved: `[p₀, q₀, r₀, s₀, p₁, q₁, r₁, s₁, …]`. -/
def quad (ps qs rs ss : List α) : List α := interleave (interleave ps rs) (interleave qs ss)

/-- Every list of length `4m` is four interleaved lists of length `m`. -/
theorem eq_quad (xs : List α) (h : xs.length = 4 * m) :
    xs = quad (evensIdx (evensIdx xs)) (evensIdx (oddsIdx xs))
      (oddsIdx (evensIdx xs)) (oddsIdx (oddsIdx xs)) := by
  rw [quad, interleave_evensIdx_oddsIdx _ (by simp; omega),
    interleave_evensIdx_oddsIdx _ (by simp; omega), interleave_evensIdx_oddsIdx _ (by omega)]

theorem length_quad_parts (xs : List α) (h : xs.length = 4 * m) :
    (evensIdx (evensIdx xs)).length = m ∧ (evensIdx (oddsIdx xs)).length = m ∧
      (oddsIdx (evensIdx xs)).length = m ∧ (oddsIdx (oddsIdx xs)).length = m := by
  simp only [length_evensIdx, length_oddsIdx, h]; omega

theorem unriffle_quad (ps qs rs ss : List α) (h₁ : ps.length = rs.length)
    (h₂ : qs.length = ss.length) (h₃ : ps.length = qs.length) :
    unriffle (quad ps qs rs ss) = interleave ps rs ++ interleave qs ss :=
  unriffle_interleave _ _ (by simp; omega)

/-- `alt` swaps the third and fourth list. -/
theorem altAux_quad : ∀ (ps qs rs ss : List α), ps.length = qs.length →
    qs.length = rs.length → rs.length = ss.length →
    altAux false (quad ps qs rs ss) = quad ps qs ss rs
  | [], [], [], [], _, _, _ => rfl
  | p :: ps, q :: qs, r :: rs, s :: ss, h₁, h₂, h₃ => by
    simp only [quad, interleave, altAux, Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true, List.cons_append, List.nil_append]
    have := altAux_quad ps qs rs ss (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)
    simp only [quad] at this
    rw [this]
  | [], _ :: _, _, _, h, _, _ => absurd h (by simp)
  | _ :: _, [], _, _, h, _, _ => absurd h (by simp)
  | [], [], _ :: _, _, _, h, _ => absurd h (by simp)
  | _ :: _, _ :: _, [], _, _, h, _ => absurd h (by simp)
  | [], [], [], _ :: _, _, _, h => absurd h (by simp)
  | _ :: _, _ :: _, _ :: _, [], _, _, h => absurd h (by simp)

/-! ## Laws of the wirings -/

/-- **W3.** Unriffling inside `ilv`, then in both halves, is unriffling twice. -/
theorem ilv_unriffle_two_unriffle (xs : List α) (h : xs.length = 4 * m) :
    two unriffle (ilv unriffle xs) = unriffle (unriffle xs) := by
  obtain ⟨hp, hq, hr, hs⟩ := length_quad_parts xs h
  rw [eq_quad xs h]
  generalize evensIdx (evensIdx xs) = ps at *
  generalize evensIdx (oddsIdx xs) = qs at *
  generalize oddsIdx (evensIdx xs) = rs at *
  generalize oddsIdx (oddsIdx xs) = ss at *
  simp only [seq_apply, ilv]
  rw [unriffle_quad _ _ _ _ (by omega) (by omega) (by omega),
    two_append _ _ _ (by simp; omega), unriffle_interleave _ _ (by omega),
    unriffle_interleave _ _ (by omega), riffle_append _ _ (by simp; omega),
    interleave_append _ _ _ _ (by omega), two_append _ _ _ (by simp; omega),
    unriffle_interleave _ _ (by omega), unriffle_interleave _ _ (by omega), unriffle,
    evensIdx_append _ _ (by simp; omega), oddsIdx_append _ _ (by simp; omega),
    evensIdx_interleave _ _ (by omega), evensIdx_interleave _ _ (by omega),
    oddsIdx_interleave _ _ (by omega), oddsIdx_interleave _ _ (by omega)]

theorem unriffle_append (xs ys : List α) (h : xs.length % 2 = 0) :
    unriffle (xs ++ ys) = (evensIdx xs ++ evensIdx ys) ++ (oddsIdx xs ++ oddsIdx ys) := by
  rw [unriffle, evensIdx_append _ _ h, oddsIdx_append _ _ h]

/-- **W6.** `ilv` and `two` commute. -/
theorem ilv_two (g : Circuit α) (hg : LP g) (xs : List α) (h : xs.length = 4 * m) :
    ilv (two g) xs = two (ilv g) xs := by
  have h₁ : (xs.take (2 * m)).length = 2 * m := by simp; omega
  have h₂ : (xs.drop (2 * m)).length = 2 * m := by simp; omega
  rw [← List.take_append_drop (2 * m) xs]
  generalize xs.take (2 * m) = X₁ at *
  generalize xs.drop (2 * m) = X₂ at *
  have hE₁ : (evensIdx X₁).length = m := by simp; omega
  have hE₂ : (evensIdx X₂).length = m := by simp; omega
  have hO₁ : (oddsIdx X₁).length = m := by simp; omega
  have hO₂ : (oddsIdx X₂).length = m := by simp; omega
  have lhs : ilv (two g) (X₁ ++ X₂) = interleave (g (evensIdx X₁)) (g (oddsIdx X₁)) ++
      interleave (g (evensIdx X₂)) (g (oddsIdx X₂)) := by
    simp only [ilv, seq_apply]
    rw [unriffle_append X₁ X₂ (by omega),
      two_append (two g) (evensIdx X₁ ++ evensIdx X₂) (oddsIdx X₁ ++ oddsIdx X₂) (by simp; omega),
      two_append g (evensIdx X₁) (evensIdx X₂) (by omega),
      two_append g (oddsIdx X₁) (oddsIdx X₂) (by omega),
      riffle_append _ _ (by simp [hg _]; omega),
      interleave_append _ _ _ _ (by simp [hg _]; omega)]
  have rhs : two (ilv g) (X₁ ++ X₂) = interleave (g (evensIdx X₁)) (g (oddsIdx X₁)) ++
      interleave (g (evensIdx X₂)) (g (oddsIdx X₂)) := by
    rw [two_append (ilv g) X₁ X₂ (by omega)]
    simp only [ilv, seq_apply, unriffle]
    rw [two_append g (evensIdx X₁) (oddsIdx X₁) (by omega),
      two_append g (evensIdx X₂) (oddsIdx X₂) (by omega),
      riffle_append (g (evensIdx X₁)) _ (by simp [hg _]; omega),
      riffle_append (g (evensIdx X₂)) _ (by simp [hg _]; omega)]
  rw [lhs, rhs]

theorem drop_length_sub_one' (l : List α) (h : l ≠ []) :
    l.drop (l.length - 1) = [l.getLast h] := by
  have e := congrArg (List.drop l.dropLast.length) (List.dropLast_concat_getLast h).symm
  rw [List.drop_left] at e
  rw [show l.length - 1 = l.dropLast.length by simp]
  exact e

theorem mid_cons (g : Circuit α) (a : α) (rest : List α) (h : rest ≠ []) :
    mid g (a :: rest) = a :: g rest.dropLast ++ [rest.getLast h] := by
  have hl : 1 ≤ rest.length := List.length_pos_iff.2 h
  have hd : List.drop rest.length (a :: rest) = [rest.getLast h] := by
    obtain ⟨k, hk⟩ : ∃ k, rest.length = k + 1 := ⟨rest.length - 1, by omega⟩
    rw [hk, List.drop_succ_cons, show k = rest.length - 1 by omega, drop_length_sub_one' rest h]
  unfold mid
  rw [ite_eq_right (by simp; omega)]
  simp only [List.length_cons, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, Nat.add_sub_cancel, List.cons_append, List.nil_append]
  rw [show rest.length + 1 - 2 = rest.length - 1 by omega, ← List.dropLast_eq_take, hd]

theorem mid_altAux_cons4 (a b c d : α) (L : List α) (hL : L.length % 4 = 0) :
    mid (altAux true) (a :: b :: c :: d :: L) = a :: c :: b :: d :: mid (altAux true) L := by
  cases L with
  | nil => rfl
  | cons e L' =>
    have hL' : L' ≠ [] := by rintro rfl; simp at hL
    rw [mid_cons _ _ _ (by simp), mid_cons _ _ _ hL']
    have hlast : (b :: c :: d :: e :: L').getLast (by simp) = L'.getLast hL' := by
      rw [List.getLast_cons (by simp), List.getLast_cons (by simp), List.getLast_cons (by simp),
        List.getLast_cons hL']
    simp only [List.dropLast_cons_of_ne_nil (by simp : (c :: d :: e :: L') ≠ []),
      List.dropLast_cons_of_ne_nil (by simp : (d :: e :: L') ≠ []),
      List.dropLast_cons_of_ne_nil (by simp : (e :: L') ≠ []),
      List.dropLast_cons_of_ne_nil hL', altAux, ite_true, ite_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, List.cons_append, List.nil_append, hlast]

/-- `mid (altAux true)` swaps the second and third of four interleaved lists. -/
theorem mid_altAux_quad : ∀ (ps qs rs ss : List α), ps.length = qs.length →
    qs.length = rs.length → rs.length = ss.length →
    mid (altAux true) (quad ps qs rs ss) = quad ps rs qs ss
  | [], [], [], [], _, _, _ => rfl
  | p :: ps, q :: qs, r :: rs, s :: ss, h₁, h₂, h₃ => by
    have h₁' : ps.length = qs.length := by simpa using h₁
    have h₂' : qs.length = rs.length := by simpa using h₂
    have h₃' : rs.length = ss.length := by simpa using h₃
    have ih := mid_altAux_quad ps qs rs ss h₁' h₂' h₃'
    simp only [quad, interleave] at ih ⊢
    rw [mid_altAux_cons4 _ _ _ _ _ (by simp; omega), ih]
  | [], _ :: _, _, _, h, _, _ => absurd h (by simp)
  | _ :: _, [], _, _, h, _, _ => absurd h (by simp)
  | [], [], _ :: _, _, _, h, _ => absurd h (by simp)
  | _ :: _, _ :: _, [], _, _, h, _ => absurd h (by simp)
  | [], [], [], _ :: _, _, _, h => absurd h (by simp)
  | _ :: _, _ :: _, _ :: _, [], _, _, h => absurd h (by simp)

/-- **W4.** `ilv riffle` is `riffle` with every other middle pair swapped. -/
theorem ilv_riffle (xs : List α) (h : xs.length = 4 * m) :
    ilv riffle xs = mid (altAux true) (riffle xs) := by
  have h₁ : (xs.take (2 * m)).length = 2 * m := by simp; omega
  have h₂ : (xs.drop (2 * m)).length = 2 * m := by simp; omega
  rw [← List.take_append_drop (2 * m) xs]
  generalize xs.take (2 * m) = X₁ at *
  generalize xs.drop (2 * m) = X₂ at *
  rw [← interleave_evensIdx_oddsIdx X₁ (by omega), ← interleave_evensIdx_oddsIdx X₂ (by omega)]
  have hA : (evensIdx X₁).length = m := by simp; omega
  have hB : (oddsIdx X₁).length = m := by simp; omega
  have hC : (evensIdx X₂).length = m := by simp; omega
  have hD : (oddsIdx X₂).length = m := by simp; omega
  generalize evensIdx X₁ = A at *
  generalize oddsIdx X₁ = B at *
  generalize evensIdx X₂ = C at *
  generalize oddsIdx X₂ = D at *
  have hu : unriffle (interleave A B ++ interleave C D) = (A ++ C) ++ (B ++ D) := by
    rw [unriffle_append _ _ (by simp; omega), evensIdx_interleave A B (by omega),
      evensIdx_interleave C D (by omega), oddsIdx_interleave A B (by omega),
      oddsIdx_interleave C D (by omega)]
  simp only [ilv, seq_apply]
  rw [hu, two_append riffle (A ++ C) (B ++ D) (by simp; omega), riffle_append A C (by omega),
    riffle_append B D (by omega), riffle_append (interleave A C) (interleave B D) (by simp; omega),
    riffle_append (interleave A B) (interleave C D) (by simp; omega)]
  have := mid_altAux_quad A C B D (by omega) (by omega) (by omega)
  simp only [quad] at this
  rw [this]

/-- The odd positions, reversed. -/
def oddsRev : Circuit α := unriffle >-> parl id List.reverse >-> riffle

/-- **W5.** The wiring at the heart of the balanced merger. -/
theorem alt_ilv_unriffle_ilv_rev (xs : List α) (h : xs.length = 4 * m) :
    ilv (parl id List.reverse) (ilv unriffle (alt xs)) =
      oddsRev (parl id List.reverse (unriffle xs)) := by
  obtain ⟨hp, hq, hr, hs⟩ := length_quad_parts xs h
  rw [eq_quad xs h]
  generalize evensIdx (evensIdx xs) = P at *
  generalize evensIdx (oddsIdx xs) = Q at *
  generalize oddsIdx (evensIdx xs) = R at *
  generalize oddsIdx (oddsIdx xs) = S at *
  have lhs : ilv (parl id List.reverse) (ilv unriffle (alt (quad P Q R S))) =
      interleave P Q ++ interleave S.reverse R.reverse := by
    have e₁ : ilv unriffle (alt (quad P Q R S)) = interleave P Q ++ interleave S R := by
      simp only [alt, ilv, seq_apply]
      rw [altAux_quad P Q R S (by omega) (by omega) (by omega),
        unriffle_quad P Q S R (by omega) (by omega) (by omega),
        two_append unriffle (interleave P S) (interleave Q R) (by simp; omega),
        unriffle_interleave P S (by omega), unriffle_interleave Q R (by omega),
        riffle_append (P ++ S) (Q ++ R) (by simp; omega), interleave_append P Q S R (by omega)]
    rw [e₁]
    simp only [ilv, seq_apply]
    rw [unriffle_append _ _ (by simp; omega), evensIdx_interleave P Q (by omega),
      evensIdx_interleave S R (by omega), oddsIdx_interleave P Q (by omega),
      oddsIdx_interleave S R (by omega),
      two_append (parl id List.reverse) (P ++ S) (Q ++ R) (by simp; omega),
      parl_append id List.reverse P S (by omega), parl_append id List.reverse Q R (by omega)]
    simp only [id]
    rw [riffle_append (P ++ S.reverse) (Q ++ R.reverse) (by simp; omega),
      interleave_append P Q S.reverse R.reverse (by omega)]
  have rhs : oddsRev (parl id List.reverse (unriffle (quad P Q R S))) =
      interleave P Q ++ interleave S.reverse R.reverse := by
    rw [unriffle_quad P Q R S (by omega) (by omega) (by omega),
      parl_append id List.reverse (interleave P R) (interleave Q S) (by simp; omega),
      reverse_interleave Q S (by omega)]
    simp only [id, oddsRev, seq_apply]
    rw [unriffle_append _ _ (by simp; omega), evensIdx_interleave P R (by omega),
      evensIdx_interleave S.reverse Q.reverse (by simp; omega), oddsIdx_interleave P R (by omega),
      oddsIdx_interleave S.reverse Q.reverse (by simp; omega),
      parl_append id List.reverse (P ++ S.reverse) (R ++ Q.reverse) (by simp; omega)]
    simp only [id, List.reverse_append, List.reverse_reverse]
    rw [riffle_append (P ++ S.reverse) (Q ++ R.reverse) (by simp; omega),
      interleave_append P Q S.reverse R.reverse (by omega)]
  rw [lhs, rhs]

/-! ## A symmetric component ignores swaps inside its pair -/

/-- Swap every pair. -/
def swapPairs : Circuit α
  | a :: b :: cs => b :: a :: swapPairs cs
  | l => l

theorem evens_altAux {f : Circuit α} (hf : Symm f) : ∀ (s : Bool) (xs : List α),
    evens f (altAux s xs) = evens f xs
  | _, [] => rfl
  | _, [_] => rfl
  | s, a :: b :: cs => by
    cases s <;> simp only [altAux, ite_true, ite_false, Bool.false_eq_true, List.cons_append,
      List.nil_append, evens, evens_altAux hf _ cs, hf b a]

theorem evens_swapPairs {f : Circuit α} (hf : Symm f) : ∀ xs : List α,
    evens f (swapPairs xs) = evens f xs
  | [] => rfl
  | [_] => rfl
  | a :: b :: cs => by simp only [swapPairs, evens, evens_swapPairs hf cs, hf b a]

theorem interleave_swap : ∀ as bs : List α, as.length = bs.length →
    interleave bs as = swapPairs (interleave as bs)
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [interleave, swapPairs, interleave_swap as bs (by simpa using h)]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

theorem mid_mid {g h : Circuit α} (xs : List α) :
    mid h (mid g xs) = mid (g >-> h) xs := by
  match xs with
  | [] => rfl
  | [a] => rfl
  | a :: b :: cs =>
    rw [mid_cons g a (b :: cs) (by simp), List.cons_append, mid_cons h a _ (by simp),
      List.dropLast_concat, List.getLast_concat, mid_cons _ a (b :: cs) (by simp)]
    rfl

/-- A butterfly of symmetric components does not see its input reversed. -/
theorem unriffle_reverse (xs : List α) (h : xs.length % 2 = 0) :
    unriffle xs.reverse = (oddsIdx xs).reverse ++ (evensIdx xs).reverse := by
  calc unriffle xs.reverse = unriffle (interleave (evensIdx xs) (oddsIdx xs)).reverse := by
        rw [interleave_evensIdx_oddsIdx xs h]
    _ = (oddsIdx xs).reverse ++ (evensIdx xs).reverse := by
        rw [reverse_interleave _ _ (by simp; omega), unriffle_interleave _ _ (by simp; omega)]

theorem bfly_reverse {f : Circuit α} (hf : Symm f) (hl : LP f) :
    ∀ (n : Nat) (xs : List α), xs.length = 2 ^ n → bfly n f xs.reverse = bfly n f xs
  | 0, xs, h => by match xs, h with | [_], _ => rfl
  | 1, xs, h => by match xs, h with | [a, b], _ => exact hf b a
  | n + 2, xs, h => by
    have hp : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
    have hE : (evensIdx xs).length = 2 ^ (n + 1) := by simp; omega
    have hO : (oddsIdx xs).length = 2 ^ (n + 1) := by simp; omega
    have hB := LP.bfly hl (n + 1)
    simp only [bfly, seq_apply, ilv]
    rw [unriffle_reverse xs (by omega),
      two_append _ (oddsIdx xs).reverse (evensIdx xs).reverse (by simp; omega),
      bfly_reverse hf hl (n + 1) _ hO, bfly_reverse hf hl (n + 1) _ hE,
      riffle_append _ _ (by simp [hB _]; omega), interleave_swap _ _ (by simp [hB _]; omega),
      evens_swapPairs hf, unriffle, two_append _ _ _ (by omega),
      riffle_append _ _ (by simp [hB _]; omega)]

/-! ## Functor laws and congruence -/

theorem two_seq {g h : Circuit α} (hg : LP g) (xs : List α) (hx : xs.length = 2 * k) :
    two (g >-> h) xs = two h (two g xs) := by
  rw [← List.take_append_drop k xs]
  have h₁ : (xs.take k).length = k := by simp; omega
  have h₂ : (xs.drop k).length = k := by simp; omega
  rw [two_append _ _ _ (by omega), two_append _ _ _ (by omega),
    two_append _ _ _ (by rw [hg, hg]; omega)]
  rfl

theorem ilv_seq {g h : Circuit α} (hg : LP g) (xs : List α) (hx : xs.length = 2 * k) :
    ilv (g >-> h) xs = ilv h (ilv g xs) := by
  simp only [ilv, seq_apply]
  rw [unriffle_riffle _ (by simp [(LP.two hg) _]; omega),
    two_seq hg _ (by simp; omega)]

theorem two_congr {g g' : Circuit α} (hgg : g ≈[k] g') : two g ≈[2 * k] two g' := by
  intro xs hx
  rw [← List.take_append_drop k xs, two_append _ _ _ (by simp; omega),
    two_append _ _ _ (by simp; omega), hgg _ (by simp; omega), hgg _ (by simp; omega)]

theorem ilv_congr {g g' : Circuit α} (hgg : g ≈[k] g') : ilv g ≈[2 * k] ilv g' := by
  intro xs hx
  simp only [ilv, seq_apply]
  rw [two_congr hgg _ (by simp; omega)]

theorem que_congr {g g' : Circuit α} (hgg : g ≈[k] g') : que g ≈[2 * k] que g' := by
  intro xs hx
  simp only [que, seq_apply]
  rw [two_congr hgg _ (by simp [(LP.ilv LP.unriffle) _]; omega)]

theorem ilv_riffle_unriffle (xs : List α) (hx : xs.length = 4 * k) :
    ilv unriffle (ilv riffle xs) = xs := by
  rw [← ilv_seq LP.riffle xs (k := 2 * k) (by omega)]
  simp only [ilv, seq_apply]
  have hid : two (riffle >-> unriffle) (unriffle xs) = unriffle xs := by
    rw [← List.take_append_drop (2 * k) (unriffle xs), two_append _ _ _ (by simp; omega)]
    simp only [seq_apply]
    rw [unriffle_riffle _ (by simp; omega), unriffle_riffle _ (by simp; omega)]
  rw [hid, riffle_unriffle _ (by omega)]

theorem que_seq {g h : Circuit α} (hg : LP g) (xs : List α) (hx : xs.length = 4 * k) :
    que (g >-> h) xs = que h (que g xs) := by
  simp only [que, seq_apply]
  rw [ilv_riffle_unriffle _ (by simp [(LP.two hg) _, (LP.ilv LP.unriffle) _]; omega),
    two_seq (k := 2 * k) hg _ (by simp [(LP.ilv LP.unriffle) _]; omega)]

theorem hrep_congr {g g' : Circuit α} (hg : LP g) (hgg : g ≈[N] g') :
    ∀ k, hrep k g ≈[N] hrep k g'
  | 0 => fun _ _ => rfl
  | k + 1 => fun xs hx => by
    simp only [hrep, seq_apply]
    rw [hgg xs hx, hrep_congr hg hgg k _ (by rw [← hgg xs hx, hg]; exact hx)]

/-! ## More lengths -/

theorem LP.vee {f : Circuit α} (hf : LP f) : LP (vee f) := (LP.alt.seq hf.ilv).seq LP.alt

theorem LP.que {f : Circuit α} (hf : LP f) : LP (que f) :=
  ((LP.unriffle.ilv).seq hf.two).seq LP.riffle.ilv

theorem LP.vfly {f : Circuit α} (hf : LP f) : ∀ n, LP (vfly n f)
  | 0 => LP.id
  | 1 => hf
  | n + 2 => (LP.vfly hf (n + 1)).vee.seq hf.evens

theorem LP.qfly {f : Circuit α} (hf : LP f) : ∀ n, LP (qfly n f)
  | 0 => LP.id
  | 1 => hf
  | n + 2 => (LP.qfly hf (n + 1)).que.seq hf.evens.mid

theorem LP.sortB {cmp : Circuit α} (hc : LP cmp) : ∀ n, LP (sortB n cmp)
  | 0 => LP.id
  | n + 1 => ((LP.sortB hc n).parl ((LP.sortB hc n).seq LP.reverse)).seq (LP.bfly hc (n + 1))

/-! ## One schema for the four mergers -/

/-- A butterfly-shaped merger: a connection pattern `P` around the merger of
half the size, then a last column `L`. -/
def fly (P L : Circuit α → Circuit α) : Nat → Circuit α → Circuit α
  | 0, _ => id
  | 1, f => f
  | n + 2, f => P (fly P L (n + 1) f) >-> L f

theorem bfly_eq_fly : ∀ n (f : Circuit α), bfly n f = fly ilv evens n f
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, f => by rw [bfly, fly, bfly_eq_fly (n + 1) f]

theorem mergeOE_eq_fly : ∀ n (f : Circuit α), mergeOE n f = fly ilv (mid ∘ evens) n f
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, f => by rw [mergeOE, fly, mergeOE_eq_fly (n + 1) f]; rfl

theorem vfly_eq_fly : ∀ n (f : Circuit α), vfly n f = fly vee evens n f
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, f => by rw [vfly, fly, vfly_eq_fly (n + 1) f]

theorem qfly_eq_fly : ∀ n (f : Circuit α), qfly n f = fly que (mid ∘ evens) n f
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, f => by rw [qfly, fly, qfly_eq_fly (n + 1) f]; rfl

/-! ## The bitonic sorter has the odd–even sorter's shape -/

/-- Batcher's bitonic merger, read as a merger of two sorted halves: reverse the
second half, then run the butterfly. -/
def mergeB (n : Nat) (cmp : Circuit α) : Circuit α := parl id List.reverse >-> bfly n cmp

theorem parl_reverse {g : Circuit α} (hg : LP g) :
    parl g (g >-> List.reverse) = two g >-> parl id List.reverse := by
  funext xs
  simp only [two, parl, seq_apply, id]
  have : (g (xs.take (xs.length / 2)) ++ g (xs.drop (xs.length / 2))).length / 2 =
      (g (xs.take (xs.length / 2))).length := by simp [hg _]; omega
  rw [this, List.take_left', List.drop_left'] <;> rfl

/-- **`sortB` and `sortOE` are one recursion.** Each sorts both halves and then
merges two sorted lists. -/
theorem sortB_eq {cmp : Circuit α} (hc : LP cmp) (n : Nat) :
    sortB (n + 1) cmp = two (sortB n cmp) >-> mergeB (n + 1) cmp := by
  rw [sortB, parl_reverse (LP.sortB hc n)]
  rfl

theorem sortOE_eq (n : Nat) (cmp : Circuit α) :
    sortOE (n + 1) cmp = two (sortOE n cmp) >-> mergeOE (n + 1) cmp := rfl

/-! ## The periodic mergers are the recursive ones, behind an `unriffle` -/

theorem ilv_unriffle_riffle' (ws : List α) (h : ws.length = 4 * k) :
    ilv riffle (ilv unriffle ws) = ws := by
  rw [← ilv_seq LP.unriffle ws (k := 2 * k) (by omega)]
  simp only [ilv, seq_apply]
  have hid : two (unriffle >-> riffle) (unriffle ws) = unriffle ws := by
    rw [← List.take_append_drop (2 * k) (unriffle ws), two_append _ _ _ (by simp; omega)]
    simp only [seq_apply]
    rw [riffle_unriffle _ (by simp; omega), riffle_unriffle _ (by simp; omega)]
  rw [hid, riffle_unriffle _ (by omega)]

/-- **Canfield and Williamson's merger is Batcher's odd–even merger after an
`unriffle`.** Each step names its law. -/
theorem qfly_eq_unriffle_mergeOE {f : Circuit α} (hf : Symm f) (hl : LP f) :
    ∀ n, qfly n f ≈[2 ^ n] (unriffle >-> mergeOE n f)
  | 0 => fun xs hx => by match xs, hx with | [_], _ => rfl
  | 1 => fun xs hx => by match xs, hx with | [_, _], _ => rfl
  | n + 2 => by
    have ih := qfly_eq_unriffle_mergeOE hf hl (n + 1)
    have hM := LP.mergeOE hl (n + 1)
    have h₄ : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [Nat.pow_succ, Nat.pow_succ]; omega
    have h₂ : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
    have hL : (altAux true >-> evens f) = evens f := funext (evens_altAux hf true)
    calc qfly (n + 2) f
        = que (qfly (n + 1) f) >-> mid (evens f)                         := rfl
      _ ≈[2 ^ (n + 2)] que (unriffle >-> mergeOE (n + 1) f) >-> mid (evens f) :=  -- induction
          fun xs hx => by simp only [seq_apply]; rw [que_congr ih xs (by omega)]
      _ ≈[2 ^ (n + 2)] que unriffle >-> que (mergeOE (n + 1) f) >-> mid (evens f) :=  -- que is a functor
          fun xs hx => by simp only [seq_apply]; rw [que_seq (k := 2 ^ n) LP.unriffle xs (by omega)]
      _ ≈[2 ^ (n + 2)] ilv unriffle >-> two unriffle >-> two (mergeOE (n + 1) f) >-> ilv riffle >->
            mid (evens f) :=  -- ilv riffle undoes ilv unriffle
          fun xs hx => by
            simp only [que, seq_apply]
            rw [ilv_riffle_unriffle (k := 2 ^ n) _
              (by simp [(LP.two LP.unriffle) _, (LP.ilv LP.unriffle) _]; omega)]
      _ ≈[2 ^ (n + 2)] unriffle >-> unriffle >-> two (mergeOE (n + 1) f) >-> ilv riffle >->
            mid (evens f) :=  -- W3
          fun xs hx => by
            simp only [seq_apply]; rw [ilv_unriffle_two_unriffle (m := 2 ^ n) xs (by omega)]
      _ ≈[2 ^ (n + 2)] unriffle >-> unriffle >-> two (mergeOE (n + 1) f) >-> riffle >->
            mid (evens f) :=  -- W4, and f is symmetric
          fun xs hx => by
            simp only [seq_apply]
            rw [ilv_riffle (m := 2 ^ n) _ (by simp [(LP.two hM) _]; omega), mid_mid, hL]
      _ = unriffle >-> mergeOE (n + 2) f                                  := rfl

theorem ilv_oddsRev {B : Circuit α}
    (hB : ∀ ys : List α, ys.length = k → B ys.reverse = B ys) (xs : List α)
    (hx : xs.length = 2 * k) : ilv B (oddsRev xs) = ilv B xs := by
  simp only [ilv, oddsRev, seq_apply]
  rw [unriffle_riffle _ (by simp [(LP.id.parl LP.reverse) _]; omega),
    unriffle, parl_append _ _ _ _ (by simp; omega),
    two_append _ _ _ (by simp; omega), two_append _ _ _ (by simp; omega)]
  rw [show (id (evensIdx xs) : List α) = evensIdx xs from rfl, hB _ (by simp; omega)]

/-- **Dowd et al.'s balanced merger is Batcher's bitonic merger after an
`unriffle`.** Each step names its law. -/
theorem vfly_eq_unriffle_mergeB {f : Circuit α} (hf : Symm f) (hl : LP f) :
    ∀ n, vfly n f ≈[2 ^ n] (unriffle >-> mergeB n f)
  | 0 => fun xs hx => by
    match xs, hx with | [_], _ => simp [vfly, mergeB, parl, unriffle, evensIdx, oddsIdx, bfly]
  | 1 => fun xs hx => by
    match xs, hx with | [_, _], _ => simp [vfly, mergeB, parl, unriffle, evensIdx, oddsIdx, bfly]
  | n + 2 => by
    have ih := vfly_eq_unriffle_mergeB hf hl (n + 1)
    have hB := LP.bfly hl (n + 1)
    have h₄ : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [Nat.pow_succ, Nat.pow_succ]; omega
    have h₂ : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
    have hU : LP (unriffle >-> parl id List.reverse : Circuit α) :=
      LP.unriffle.seq (LP.id.parl LP.reverse)
    calc vfly (n + 2) f
        = alt >-> ilv (vfly (n + 1) f) >-> alt >-> evens f                := rfl
      _ ≈[2 ^ (n + 2)] alt >-> ilv (vfly (n + 1) f) >-> evens f :=  -- f is symmetric
          fun xs hx => by simp only [seq_apply, alt]; rw [evens_altAux hf]
      _ ≈[2 ^ (n + 2)] alt >-> ilv (unriffle >-> parl id List.reverse >-> bfly (n + 1) f) >->
            evens f :=  -- induction
          fun xs hx => by
            simp only [seq_apply]; rw [ilv_congr ih _ (by simp [LP.alt _]; omega)]; rfl
      _ ≈[2 ^ (n + 2)] alt >-> ilv unriffle >-> ilv (parl id List.reverse) >-> ilv (bfly (n + 1) f) >->
            evens f :=  -- ilv is a functor
          fun xs hx => by
            simp only [seq_apply]
            rw [ilv_seq (k := 2 ^ (n + 1)) hU _ (by simp [LP.alt _]; omega),
              ilv_seq (k := 2 ^ (n + 1)) LP.unriffle _ (by simp [LP.alt _]; omega)]
      _ ≈[2 ^ (n + 2)] unriffle >-> parl id List.reverse >-> oddsRev >-> ilv (bfly (n + 1) f) >->
            evens f :=  -- W5
          fun xs hx => by
            simp only [seq_apply]; rw [alt_ilv_unriffle_ilv_rev (m := 2 ^ n) xs (by omega)]
      _ ≈[2 ^ (n + 2)] unriffle >-> parl id List.reverse >-> ilv (bfly (n + 1) f) >-> evens f :=
          fun xs hx => by  -- a butterfly ignores a reversal
            simp only [seq_apply]
            rw [ilv_oddsRev (k := 2 ^ (n + 1)) (bfly_reverse hf hl (n + 1)) _
              (by simp [(LP.id.parl LP.reverse) _]; omega)]
      _ = unriffle >-> mergeB (n + 2) f                                     := rfl

/-! ## The four sorter cores -/

/-- The periodic sorter `sortQ` is `n` odd–even mergers, each behind an `unriffle`. -/
theorem sortQ_eq {f : Circuit α} (hf : Symm f) (hl : LP f) (n : Nat) :
    sortQ n f ≈[2 ^ n] hrep n (unriffle >-> mergeOE n f) :=
  hrep_congr (LP.qfly hl n) (qfly_eq_unriffle_mergeOE hf hl n) n

/-- The periodic sorter `sortV` is `n` bitonic mergers, each behind an `unriffle`. -/
theorem sortV_eq {f : Circuit α} (hf : Symm f) (hl : LP f) (n : Nat) :
    sortV n f ≈[2 ^ n] hrep n (unriffle >-> mergeB n f) :=
  hrep_congr (LP.vfly hl n) (vfly_eq_unriffle_mergeB hf hl n) n

/-! ## The paper's lemma, in the same calculus -/

theorem two_riffle_unriffle (v : List α) (h : v.length = 4 * k) :
    two riffle (two unriffle v) = v := by
  rw [← List.take_append_drop (2 * k) v, two_append _ _ _ (by simp; omega),
    two_append _ _ _ (by simp; omega), riffle_unriffle _ (by simp; omega),
    riffle_unriffle _ (by simp; omega)]

/-- W3, run backwards. -/
theorem ilv_riffle_two_riffle (zs : List α) (h : zs.length = 4 * k) :
    ilv riffle (two riffle zs) = riffle (riffle zs) := by
  have hw := ilv_unriffle_two_unriffle (m := k) (riffle (riffle zs)) (by simp; omega)
  rw [unriffle_riffle _ (by simp; omega), unriffle_riffle _ (by omega)] at hw
  calc ilv riffle (two riffle zs)
      = ilv riffle (two riffle (two unriffle (ilv unriffle (riffle (riffle zs))))) := by rw [hw]
    _ = ilv riffle (ilv unriffle (riffle (riffle zs))) := by
        rw [two_riffle_unriffle (k := k) _ (by simp [(LP.ilv LP.unriffle) _]; omega)]
    _ = riffle (riffle zs) := ilv_unriffle_riffle' (k := k) _ (by simp; omega)

/-- **The lemma of §6 of the paper:** `que (ilv f) = ilv (ilv f)`. -/
theorem que_ilv {g : Circuit α} (hg : LP g) (xs : List α) (h : xs.length = 4 * k) :
    que (ilv g) xs = ilv (ilv g) xs := by
  have h₁ : (ilv unriffle xs).length = 4 * k := by simp [(LP.ilv LP.unriffle) _, h]
  have htwo : two (ilv g) (ilv unriffle xs) =
      two riffle (two (two g) (two unriffle (ilv unriffle xs))) := by
    show two (unriffle >-> two g >-> riffle) _ = _
    rw [two_seq (k := 2 * k) (LP.unriffle.seq hg.two) _ (by omega),
      two_seq (k := 2 * k) LP.unriffle _ (by omega)]
  simp only [que, seq_apply]
  rw [htwo, ilv_unriffle_two_unriffle (m := k) xs h,
    ilv_riffle_two_riffle (k := k) _ (by simp [(LP.two hg.two) _, h]),
    show ilv (ilv g) xs = riffle (two (ilv g) (unriffle xs)) from rfl,
    ← ilv_two (m := k) g hg (unriffle xs) (by simp [h])]
  rfl

/-! ## Checks, as in §5 of the paper -/

/-- A list of bits is sorted when each bit implies the next. -/
def sorted : List Bool → Bool
  | a :: b :: cs => (!a || b) && sorted (b :: cs)
  | _ => true

/-- All `2ⁿ`-bit inputs, as lists. -/
def allInputs (n : Nat) : List (List Bool) :=
  (List.range (2 ^ (2 ^ n))).map fun k => (List.range (2 ^ n)).map k.testBit

/-- All four sorters, on bits. -/
def sortsAll (n : Nat) (xs : List Bool) : Bool :=
  sorted (sortB n twoBitSort xs) && sorted (sortOE n twoBitSort xs) &&
    sorted (sortV n twoBitSort xs) && sorted (sortQ n twoBitSort xs)

-- All four sort every 4-bit input: a kernel-checked proof. By the zero-one
-- principle, a comparator network that sorts every bit list sorts every list.
example : (allInputs 2).all (sortsAll 2) = true := by decide +kernel

-- And every 8-bit input, by evaluation.
#guard (allInputs 3).all (sortsAll 3)

-- `bflyCompose` is not a sorter: the paper's counterexample passes through unchanged.
example : bflyCompose 2 twoBitSort [false, true, false, true] = [false, true, false, true] := by
  decide

end BirdMeertens.Sorters


