import Kadane

/-!
# A parallel-prefix adder, derived from the definition of a carry

The carry into column `i` of a binary addition is set exactly when the low `i`
columns, plus the carry in, overflow `i` bits. That is the specification.

A ripple-carry adder computes the carries one column after another, so its
depth grows linearly with the width. A carry-lookahead adder computes them with
a parallel prefix network instead, in logarithmic depth.

This file derives the second from the first, Bird–Meertens style.
`carries_eq_prefixNet` is one `calc` block:

* the full-adder law turns each overflow test into a left fold;
* the scan lemma, from the Kadane derivation, turns the folds into one scan:
  the ripple-carry adder;
* scan fusion moves the scan onto generate and propagate pairs;
* their operator `⊛` is associative, so the scan can run as Sklansky's
  divide-and-conquer network.

`refine_cla_from_ripple_carry` is a second `calc` block. It relates the two
adders directly. It starts from a row of full adders, as Lava builds a
ripple-carry adder. The row law splits the row into a carry scan and one XOR
per column. The same steps then carry the scan to Sklansky's network.

The network is a function of its operator. Run on arrival times instead of
bits, the same code gives its depth: `n - 1` levels for the serial scan,
`⌈log₂ n⌉` for Sklansky.
-/

namespace BirdMeertens.Adder

open List (map foldl)

/-! ## The specification -/

/-- The value of a bit list, least significant bit first. -/
def val : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * val bs

/-- One column of an addition: a bit of each operand. -/
abbrev Col := Bool × Bool

/-- Whether the columns `ys`, plus a carry in `c`, overflow `ys.length` bits. -/
def carryOut (c : Bool) (ys : List Col) : Bool :=
  decide (2 ^ ys.length ≤ val (ys.map Prod.fst) + val (ys.map Prod.snd) + c.toNat)

/-- **The specification.** The carry into each column is the overflow of the
columns below it. There is one more carry than columns; the last is the carry out. -/
def carries (c : Bool) : List Col → List Bool := map (carryOut c) ∘ inits

/-! ## The pieces of an adder -/

/-- A full adder's carry out: the majority of its three inputs. -/
def carry (c : Bool) (x : Col) : Bool := (x.1 && x.2) || (c && (x.1 || x.2))

/-- A column's generate and propagate bits. -/
def gp (x : Col) : Bool × Bool := (x.1 && x.2, x.1 ^^ x.2)

/-- The carry out of a block with generate and propagate `q`, given carry in `c`. -/
def ev (c : Bool) (q : Bool × Bool) : Bool := q.1 || (q.2 && c)

/-- The carry operator. `a ⊛ b` is block `a` with block `b` above it. It
generates if `b` generates, or if `b` propagates what `a` generates. -/
def dot (a b : Bool × Bool) : Bool × Bool := (b.1 || (b.2 && a.1), a.2 && b.2)

local infixl:70 " ⊛ " => dot

/-- Inclusive scan: `scan1 f [x₀, x₁, x₂, …] = [x₀, f x₀ x₁, f (f x₀ x₁) x₂, …]`. -/
def scan1 (f : α → α → α) : List α → List α
  | [] => []
  | x :: xs => scanl f x xs

/-- Sklansky's parallel prefix network, with `k` levels for up to `2ᵏ` inputs.
It scans both halves at once, then combines the last result of the left half
into every result of the right half. -/
def sklansky (f : α → α → α) : Nat → List α → List α
  | 0, xs => xs
  | k + 1, xs =>
    let l := sklansky f k (xs.take (2 ^ k))
    let r := sklansky f k (xs.drop (2 ^ k))
    match l.getLast? with
    | some z => l ++ r.map (f z)
    | none => r

/-- The levels Sklansky needs for `n` inputs: `⌈log₂ n⌉`. -/
def levels (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- A Sklansky network just deep enough for its input. -/
def prefixNet (f : α → α → α) (xs : List α) : List α := sklansky f (levels xs.length) xs

/-! ## Facts about columns -/

/-- **The full-adder law.** One column's carry out feeds the columns above. -/
theorem carryOut_cons (c : Bool) (x : Col) (ys : List Col) :
    carryOut c (x :: ys) = carryOut (carry c x) ys := by
  obtain ⟨a, b⟩ := x
  simp only [carryOut, List.map_cons, val, List.length_cons, Nat.pow_succ]
  cases a <;> cases b <;> cases c <;> simp [carry, decide_eq_decide] <;> omega

theorem carryOut_eq_foldl (c : Bool) : carryOut c = foldl carry c := by
  funext ys
  induction ys generalizing c with
  | nil => cases c <;> rfl
  | cons x ys ih => rw [carryOut_cons, ih, List.foldl_cons]

/-- A carry is generated, or propagated from below. -/
theorem carry_eq_ev (c : Bool) (x : Col) : carry c x = ev c (gp x) := by
  obtain ⟨a, b⟩ := x
  cases a <;> cases b <;> cases c <;> rfl

theorem dot_assoc (a b c : Bool × Bool) : a ⊛ b ⊛ c = a ⊛ (b ⊛ c) := by
  obtain ⟨_ | _, _ | _⟩ := a <;> obtain ⟨_ | _, _ | _⟩ := b <;>
    obtain ⟨_ | _, _ | _⟩ := c <;> rfl

/-! ## Facts about scans -/

theorem scanl_ne_nil (f : β → α → β) (e : β) (xs : List α) : scanl f e xs ≠ [] := by
  cases xs <;> simp [scanl]

theorem length_scanl (f : β → α → β) (e : β) (xs : List α) :
    (scanl f e xs).length = xs.length + 1 := by
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih => simp [scanl, ih]

theorem getLast?_scanl (f : β → α → β) (e : β) (xs : List α) :
    (scanl f e xs).getLast? = some (foldl f e xs) := by
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨y, ys, h⟩ := List.exists_cons_of_ne_nil (scanl_ne_nil f (f e x) xs)
    rw [scanl, h, List.getLast?_cons_cons, ← h, ih, List.foldl_cons]

theorem scanl_append (f : β → α → β) (e : β) (xs ys : List α) :
    scanl f e (xs ++ ys) = scanl f e xs ++ (scanl f (foldl f e xs) ys).tail := by
  induction xs generalizing e with
  | nil => cases ys <;> rfl
  | cons x xs ih => simp [scanl, ih]

/-- Scanning from a combined seed, for an associative operator. -/
theorem scanl_assoc {f : α → α → α} (hf : ∀ a b c, f (f a b) c = f a (f b c))
    (a b : α) (ys : List α) : scanl f (f a b) ys = map (f a) (scanl f b ys) := by
  induction ys generalizing b with
  | nil => rfl
  | cons y ys ih => simp only [scanl, hf, ih, List.map_cons]

/-- The scan of a concatenation: scan the right part on its own, then combine
the left part's total into each of its results. -/
theorem scan1_append {f : α → α → α} (hf : ∀ a b c, f (f a b) c = f a (f b c))
    (a : α) (as bs : List α) :
    scan1 f (a :: as ++ bs) = scanl f a as ++ map (f (foldl f a as)) (scan1 f bs) := by
  cases bs with
  | nil => simp [scan1]
  | cons b bs =>
    simp only [List.cons_append, scan1]
    rw [scanl_append, scanl, List.tail_cons, scanl_assoc hf]

/-! ## The laws -/

/-- **Scan–map fusion.** A map before a scan joins the scan's step. -/
theorem scan_map_fusion (f : β → α → β) (e : β) (g : γ → α) :
    scanl f e ∘ map g = scanl (fun a x => f a (g x)) e := by
  funext xs
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih => simp only [Function.comp_apply, List.map_cons, scanl] at ih ⊢; rw [ih]

/-- **Scan fusion.** A function that commutes with each step commutes with the scan. -/
theorem scan_fusion {f : β → α → β} {f' : γ → α → γ} {e : β} {e' : γ} (h : β → γ)
    (hseed : h e = e') (hstep : ∀ a x, h (f a x) = f' (h a) x) (g : δ → List α) :
    map h ∘ scanl f e ∘ g = scanl f' e' ∘ g := by
  funext d
  simp only [Function.comp_apply]
  generalize g d = xs
  induction xs generalizing e e' with
  | nil => simp [scanl, hseed]
  | cons x xs ih =>
    have := ih (e := f e x) (e' := f' e' x) (by rw [hstep, hseed])
    simp only [scanl, List.map_cons, hseed, this]

/-- **Parallel prefix.** For an associative operator, Sklansky's network computes
the scan. -/
theorem sklansky_eq_scan1 {f : α → α → α} (hf : ∀ a b c, f (f a b) c = f a (f b c)) :
    ∀ (k : Nat) (xs : List α), xs.length ≤ 2 ^ k → sklansky f k xs = scan1 f xs := by
  intro k
  induction k with
  | zero =>
    intro xs h
    match xs, h with
    | [], _ => rfl
    | [_], _ => rfl
  | succ k ih =>
    intro xs h
    have hl : (xs.take (2 ^ k)).length ≤ 2 ^ k := by simp; omega
    have hr : (xs.drop (2 ^ k)).length ≤ 2 ^ k := by simp [Nat.pow_succ] at h ⊢; omega
    simp only [sklansky, ih _ hl, ih _ hr]
    rw [show scan1 f xs = scan1 f (xs.take (2 ^ k) ++ xs.drop (2 ^ k)) by
      rw [List.take_append_drop]]
    cases ht : xs.take (2 ^ k) with
    | nil =>
      have hx : xs = [] := by
        rcases List.take_eq_nil_iff.1 ht with h' | h'
        · have := Nat.two_pow_pos k; omega
        · exact h'
      subst hx
      simp [scan1]
    | cons a as =>
      simp only [scan1.eq_2, getLast?_scanl]
      rw [← scan1.eq_2, scan1_append hf]
      rfl

theorem lt_two_pow_levels (n : Nat) : n ≤ 2 ^ levels n := by
  unfold levels
  split
  · simpa
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-- The network `prefixNet` computes the scan, for an associative operator. -/
theorem prefixNet_eq_scan1 {f : α → α → α} (hf : ∀ a b c, f (f a b) c = f a (f b c)) :
    prefixNet f = scan1 f := by
  funext xs
  exact sklansky_eq_scan1 hf _ xs (lt_two_pow_levels _)

/-! ## The derivation -/

/-- The ripple-carry adder computes the carries. -/
theorem carries_eq_ripple (c : Bool) : carries c = scanl carry c := by
  rw [carries, carryOut_eq_foldl, scan_lemma]

/-- The carries come out of a Sklansky prefix network. Each step names its law.
On the right is the depth of the carry chain, for `n` columns. -/
theorem carries_eq_prefixNet (c : Bool) :
    carries c = map Prod.fst ∘ prefixNet (· ⊛ ·) ∘ ((c, false) :: ·) ∘ map gp :=
  calc carries c
      = map (carryOut c) ∘ inits                                := rfl  -- the specification
    _ = map (foldl carry c) ∘ inits                             := by rw [carryOut_eq_foldl]
    _ = scanl carry c                                           := scan_lemma carry c  -- n
    _ = scanl ev c ∘ map gp                                     := by
          rw [scan_map_fusion]; congr 1; funext a x; exact carry_eq_ev a x
    _ = map Prod.fst ∘ scanl (· ⊛ ·) (c, false) ∘ map gp        :=
          (scan_fusion (f := (· ⊛ ·)) (f' := ev) (e := (c, false)) (e' := c) Prod.fst rfl
            (fun _ _ => rfl) (map gp)).symm
    _ = map Prod.fst ∘ scan1 (· ⊛ ·) ∘ ((c, false) :: ·) ∘ map gp := rfl
    _ = map Prod.fst ∘ prefixNet (· ⊛ ·) ∘ ((c, false) :: ·) ∘ map gp := by
          rw [prefixNet_eq_scan1 dot_assoc]  -- ⌈log₂ (n + 1)⌉

/-! ## The adder -/

/-- The sum bits from the carries, `pᵢ ⊕ cᵢ`, then the carry out. -/
def sumBits (xs : List Col) (cs : List Bool) : List Bool :=
  List.zipWith (fun x c => (x.1 ^^ x.2) ^^ c) xs cs ++ [cs.getLast?.getD false]

/-- The carry-lookahead adder: generate and propagate per column, a Sklansky
prefix network for the carries, then one XOR per column. -/
def cla (c : Bool) (xs : List Col) : List Bool :=
  sumBits xs ((map Prod.fst ∘ prefixNet (· ⊛ ·) ∘ ((c, false) :: ·) ∘ map gp) xs)

theorem sumBits_cons (x : Col) (xs : List Col) (c : Bool) (cs : List Bool) (h : cs ≠ []) :
    sumBits (x :: xs) (c :: cs) = ((x.1 ^^ x.2) ^^ c) :: sumBits xs cs := by
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [sumBits, List.getLast?_cons_cons]

theorem val_sumBits_ripple (c : Bool) (xs : List Col) :
    val (sumBits xs (scanl carry c xs)) =
      val (xs.map Prod.fst) + val (xs.map Prod.snd) + c.toNat := by
  induction xs generalizing c with
  | nil => simp [sumBits, scanl, val]
  | cons x xs ih =>
    rw [scanl, sumBits_cons _ _ _ _ (scanl_ne_nil _ _ _)]
    simp only [val, ih, List.map_cons]
    obtain ⟨a, b⟩ := x
    cases a <;> cases b <;> cases c <;> simp [carry] <;> omega

/-- **The carry-lookahead adder adds.** Its output, read as a number, is the sum. -/
theorem cla_correct (c : Bool) (xs : List Col) :
    val (cla c xs) = val (xs.map Prod.fst) + val (xs.map Prod.snd) + c.toNat := by
  rw [cla, ← carries_eq_prefixNet, carries_eq_ripple, val_sumBits_ripple]

/-- It has one more bit than each operand, so nothing is lost. -/
theorem length_cla (c : Bool) (xs : List Col) : (cla c xs).length = xs.length + 1 := by
  rw [cla, ← carries_eq_prefixNet, carries_eq_ripple]
  simp [sumBits, length_scanl]

/-! ## From ripple-carry to carry-lookahead

The derivation above is about carries. This one is about whole adders. It
starts from the ripple-carry adder as Lava builds it, a row of full adders, and
ends at `cla`. Neither end mentions the specification. -/

/-- Lava's `row`: a chain of cells, left to right. Each cell takes a carry from
its left and passes one to its right. The result is the cells' outputs and the
last carry. -/
def row (f : γ → α → β × γ) : γ → List α → List β × γ
  | c, [] => ([], c)
  | c, x :: xs =>
    let r := row f (f c x).2 xs
    ((f c x).1 :: r.1, r.2)

/-- A full adder: the sum bit and the carry out of one column. -/
def fullAdd (c : Bool) (x : Col) : Bool × Bool := ((x.1 ^^ x.2) ^^ c, carry c x)

/-- Put the last carry on top of the outputs. -/
def snoc (r : List Bool × Bool) : List Bool := r.1 ++ [r.2]

/-- **The ripple-carry adder**: a row of full adders. The last carry is the top bit. -/
def ripple (c : Bool) : List Col → List Bool := snoc ∘ row fullAdd c

/-- An adder around a carry network `net`: one XOR per column, then the carry out. -/
def adder (net : List Col → List Bool) (xs : List Col) : List Bool := sumBits xs (net xs)

/-- **The row law.** The carries along a row are a scan. Each output reads its
column and the carry into it. -/
theorem row_eq_scan (f : γ → α → β × γ) (c : γ) (xs : List α) :
    row f c xs = (List.zipWith (fun x c => (f c x).1) xs (scanl (fun c x => (f c x).2) c xs),
      foldl (fun c x => (f c x).2) c xs) := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [row, ih, scanl, List.zipWith_cons_cons, List.foldl_cons]

/-- A row of full adders is a carry chain, then one XOR per column. -/
theorem row_fullAdd (c : Bool) : snoc ∘ row fullAdd c = adder (scanl carry c) := by
  funext xs
  simp only [Function.comp_apply, row_eq_scan, snoc, adder, sumBits, getLast?_scanl,
    Option.getD_some, fullAdd]

/-- **Step-wise refine a carry-lookahead adder from a ripple-carry adder.**
Each step names its law. On the right is the depth of the carry chain, for `n` columns. -/
theorem refine_cla_from_ripple_carry (c : Bool) : ripple c = cla c :=
  calc ripple c
      = snoc ∘ row fullAdd c                                            := rfl  -- n
    _ = adder (scanl carry c)                                           := row_fullAdd c
    _ = adder (scanl ev c ∘ map gp)                                     := by
          rw [scan_map_fusion]; congr; funext a x; exact carry_eq_ev a x
    _ = adder (map Prod.fst ∘ scanl (· ⊛ ·) (c, false) ∘ map gp)        := congrArg adder
          (scan_fusion (f := (· ⊛ ·)) (f' := ev) (e := (c, false)) (e' := c) Prod.fst rfl
            (fun _ _ => rfl) (map gp)).symm
    _ = adder (map Prod.fst ∘ scan1 (· ⊛ ·) ∘ ((c, false) :: ·) ∘ map gp) := rfl
    _ = adder (map Prod.fst ∘ prefixNet (· ⊛ ·) ∘ ((c, false) :: ·) ∘ map gp) := by
          rw [prefixNet_eq_scan1 dot_assoc]  -- ⌈log₂ (n + 1)⌉
    _ = cla c                                                           := rfl

/-! ## Depth

The network takes its operator as an argument. Give it `later` and arrival
times instead of `⊛` and bits, and it computes how many levels of prefix nodes
each output waits for. `later` is not associative, so the two networks differ. -/

/-- A prefix node is ready one level after its later input. -/
def later (t u : Nat) : Nat := max t u + 1

theorem foldl_later (s n : Nat) : foldl later s (List.replicate n 0) = s + n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.foldl_cons, ih, later]; omega

/-- The serial scan, which is the ripple-carry chain: its last output waits
`n` levels on `n + 1` inputs. -/
theorem serial_depth (n : Nat) : (scan1 later (List.replicate (n + 1) 0)).getLast? = some n := by
  rw [List.replicate_succ, scan1, getLast?_scanl, foldl_later]
  simp

theorem sklansky_depth :
    ∀ (k : Nat) (xs : List Nat), xs.length ≤ 2 ^ k → (∀ t ∈ xs, t = 0) →
      ∀ t ∈ sklansky later k xs, t ≤ k := by
  intro k
  induction k with
  | zero => intro xs _ h0 t ht; simp [h0 t ht]
  | succ k ih =>
    intro xs h h0
    have hl := ih (xs.take (2 ^ k)) (by simp; omega) fun t ht => h0 t (List.mem_of_mem_take ht)
    have hr := ih (xs.drop (2 ^ k)) (by simp [Nat.pow_succ] at h ⊢; omega)
      fun t ht => h0 t (List.mem_of_mem_drop ht)
    simp only [sklansky]
    split
    · next z hz =>
      have hzk := hl z (List.mem_of_getLast? hz)
      intro t ht
      simp only [List.mem_append, List.mem_map] at ht
      rcases ht with ht | ⟨u, hu, rfl⟩
      · exact Nat.le_succ_of_le (hl t ht)
      · have := hr u hu
        simp only [later]
        omega
    · intro t ht
      exact Nat.le_succ_of_le (hr t ht)

/-- Sklansky's network: every output waits at most `⌈log₂ n⌉` levels on `n` inputs. -/
theorem prefixNet_depth (n : Nat) : ∀ t ∈ prefixNet later (List.replicate n 0), t ≤ levels n := by
  have := sklansky_depth (levels n) (List.replicate n 0) (by simpa using lt_two_pow_levels n)
    (fun t ht => (List.eq_of_mem_replicate ht))
  simpa [prefixNet] using this

/-! ## A netlist from the same network

`prefixNet` takes its operator as an argument, so it builds circuits too. Run on
symbolic signals, it returns a gate-level netlist. `claNet_correct` proves that
the netlist adds. `lake exe adder_netlist` prints it as Verilog. -/

/-- A signal in a netlist of two-input gates. -/
inductive Sig where
  | input (name : String)
  | const (b : Bool)
  | and (a b : Sig)
  | or (a b : Sig)
  | xor (a b : Sig)
  deriving BEq, Hashable, Inhabited

/-- The value of a signal, given values for the inputs. -/
def Sig.eval (env : String → Bool) : Sig → Bool
  | .input n => env n
  | .const b => b
  | .and a b => a.eval env && b.eval env
  | .or a b => a.eval env || b.eval env
  | .xor a b => a.eval env ^^ b.eval env

/-- The value of a pair of signals. -/
def evalPair (env : String → Bool) (x : Sig × Sig) : Bool × Bool := (x.1.eval env, x.2.eval env)

/-- `carry`, built from gates. -/
def carryNet (c : Sig) (x : Sig × Sig) : Sig := .or (.and x.1 x.2) (.and c (.or x.1 x.2))

/-- `gp`, built from gates. -/
def gpNet (x : Sig × Sig) : Sig × Sig := (.and x.1 x.2, .xor x.1 x.2)

/-- `⊛`, built from gates. -/
def dotNet (a b : Sig × Sig) : Sig × Sig := (.or b.1 (.and b.2 a.1), .and a.2 b.2)

/-- `sumBits`, built from gates. -/
def sumBitsNet (xs : List (Sig × Sig)) (cs : List Sig) : List Sig :=
  List.zipWith (fun x c => .xor (.xor x.1 x.2) c) xs cs ++ [cs.getLast?.getD (.const false)]

/-- The ripple-carry adder as a netlist: the third line of the derivation. -/
def rippleNet (c : Sig) (xs : List (Sig × Sig)) : List Sig := sumBitsNet xs (scanl carryNet c xs)

/-- The carry-lookahead adder as a netlist: the last line of the derivation. -/
def claNet (c : Sig) (xs : List (Sig × Sig)) : List Sig :=
  sumBitsNet xs ((map Prod.fst ∘ prefixNet dotNet ∘ ((c, .const false) :: ·) ∘ map gpNet) xs)

/-- Sklansky's network commutes with any map that respects the operator. -/
theorem map_sklansky {f : α → α → α} {g : β → β → β} (h : α → β)
    (hh : ∀ a b, h (f a b) = g (h a) (h b)) :
    ∀ (k : Nat) (xs : List α), map h (sklansky f k xs) = sklansky g k (map h xs) := by
  intro k
  induction k with
  | zero => intro xs; rfl
  | succ k ih =>
    intro xs
    simp only [sklansky, ← List.map_take, ← List.map_drop, ← ih, List.getLast?_map]
    cases (sklansky f k (List.take (2 ^ k) xs)).getLast? <;> simp [hh]

theorem map_prefixNet {f : α → α → α} {g : β → β → β} (h : α → β)
    (hh : ∀ a b, h (f a b) = g (h a) (h b)) (xs : List α) :
    map h (prefixNet f xs) = prefixNet g (map h xs) := by
  simp only [prefixNet, map_sklansky h hh, List.length_map]

theorem map_sumBitsNet (env : String → Bool) (xs : List (Sig × Sig)) (cs : List Sig) :
    map (Sig.eval env) (sumBitsNet xs cs) = sumBits (map (evalPair env) xs) (map (Sig.eval env) cs) := by
  simp only [sumBitsNet, sumBits, List.map_append, List.map_cons, List.map_nil, List.map_zipWith,
    List.zipWith_map, List.getLast?_map]
  cases cs.getLast? <;> rfl

theorem map_scanl_carryNet (env : String → Bool) (c : Sig) (xs : List (Sig × Sig)) :
    map (Sig.eval env) (scanl carryNet c xs) = scanl carry (c.eval env) (map (evalPair env) xs) := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [scanl, List.map_cons, ih]; rfl

/-- **The ripple netlist adds.** -/
theorem rippleNet_correct (env : String → Bool) (c : Sig) (xs : List (Sig × Sig)) :
    val (map (Sig.eval env) (rippleNet c xs)) =
      val (xs.map (·.1.eval env)) + val (xs.map (·.2.eval env)) + (c.eval env).toNat := by
  rw [rippleNet, map_sumBitsNet, map_scanl_carryNet, val_sumBits_ripple]
  simp only [List.map_map]
  rfl

/-- **The carry-lookahead netlist adds.** -/
theorem claNet_correct (env : String → Bool) (c : Sig) (xs : List (Sig × Sig)) :
    val (map (Sig.eval env) (claNet c xs)) =
      val (xs.map (·.1.eval env)) + val (xs.map (·.2.eval env)) + (c.eval env).toNat := by
  have h : map (Sig.eval env) ((map Prod.fst ∘ prefixNet dotNet ∘ ((c, .const false) :: ·) ∘
      map gpNet) xs) = (map Prod.fst ∘ prefixNet (· ⊛ ·) ∘ ((c.eval env, false) :: ·) ∘ map gp)
      (map (evalPair env) xs) := by
    simp only [Function.comp_apply, List.map_map]
    rw [show Sig.eval env ∘ Prod.fst = Prod.fst ∘ evalPair env from rfl, ← List.map_map,
      map_prefixNet (f := dotNet) (g := (· ⊛ ·)) (evalPair env) (fun _ _ => rfl)]
    simp only [List.map_cons, List.map_map]
    rfl
  rw [claNet, map_sumBitsNet, h, ← cla, cla_correct]
  simp only [List.map_map]
  rfl

/-! ## Checks -/

/-- The low `n` bits of `m`, least significant first. -/
def bitsOf (n m : Nat) : List Bool := (List.range n).map m.testBit

example : val (cla false ((bitsOf 8 200).zip (bitsOf 8 100))) = 300 := by decide
example : val (cla true ((bitsOf 16 65535).zip (bitsOf 16 1))) = 65537 := by decide
example : val (ripple false ((bitsOf 8 200).zip (bitsOf 8 100))) = 300 := by decide

-- Levels of prefix nodes on n inputs: the serial scan, then Sklansky.
#guard [8, 16, 32, 64, 128].map (fun n =>
    ((scan1 later (List.replicate n 0)).foldl max 0,
     (prefixNet later (List.replicate n 0)).foldl max 0)) ==
  [(7, 3), (15, 4), (31, 5), (63, 6), (127, 7)]

end BirdMeertens.Adder
