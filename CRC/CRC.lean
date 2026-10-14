import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LinearCombination
import Std.Tactic.BVDecide

/-!
# A CRC, derived from its specification

The textbook definition of a cyclic redundancy check is algebraic. Read the
message bits as a polynomial `M` over GF(2). The CRC is the remainder of
`M·Xᵏ` divided by a generator `g` of degree `k`.

Hardware never divides polynomials. It clocks the bits through a `k`-bit
linear feedback shift register (LFSR). Software goes a byte at a time, with
a 256-entry table (Sarwate, 1988).

This file derives both from the definition, Bird–Meertens style:

* `crc_eq_lfsr` is one `calc` block, from the spec to the LFSR. Fold fusion
  does three jobs in it: it moves a shift, a reduction, and a change of data
  representation through the fold.
* `crcBytes_eq_table` continues to the table-driven loop, for every width `k ≥ 8`.
* `crc8Next_eq_lfsrStep` checks, with `bv_decide`, that the RTL in
  `CRC/crc8.sv` is the derived LFSR, bit for bit.

The polynomial `poly` follows the CRC catalogues. It lists every coefficient
of `g` except the leading `Xᵏ`.
-/

namespace BirdMeertens.CRC

open Polynomial
open List (map foldl flatten)

/-- The field with two elements. -/
abbrev GF2 := ZMod 2

noncomputable section

/-! ## The specification -/

/-- A bit, read as a constant polynomial. -/
def bit (b : Bool) : GF2[X] := C (if b then 1 else 0)

/-- The message polynomial. The first bit is the leading coefficient:
`msgPoly [b₀, …, bₙ₋₁] = b₀·Xⁿ⁻¹ + ⋯ + bₙ₋₁`. -/
def msgPoly : List Bool → GF2[X]
  | [] => 0
  | b :: bs => bit b * X ^ bs.length + msgPoly bs

/-- The polynomial a `k`-bit register holds. Bit `i` is the coefficient of `Xⁱ`. -/
def toPoly (r : BitVec k) : GF2[X] := ∑ i ∈ Finset.range k, bit (r.getLsbD i) * X ^ i

/-- The generator `g = Xᵏ + poly`. -/
def gen (poly : BitVec k) : GF2[X] := X ^ k + toPoly poly

/-- **The specification.** The remainder of `M·Xᵏ` divided by `g`. -/
def crc (poly : BitVec k) : List Bool → GF2[X] := (· %ₘ gen poly) ∘ (· * X ^ k) ∘ msgPoly

end

/-! ## The implementation -/

/-- One clock of the register. The message bit enters through the feedback. -/
def lfsrStep (poly : BitVec k) (r : BitVec k) (b : Bool) : BitVec k :=
  if r.msb ^^ b then (r <<< 1) ^^^ poly else r <<< 1

/-! ## Intermediate programs

Each is a left fold, so each runs as a streaming loop. Only `hornerMod` keeps
bounded state. -/

noncomputable section

/-- Horner's step: shift in one coefficient. -/
def horner (p : GF2[X]) (b : Bool) : GF2[X] := p * X + bit b

/-- Horner's step on `p·Xᵏ`. -/
def hornerShift (k : ℕ) (p : GF2[X]) (b : Bool) : GF2[X] := p * X + bit b * X ^ k

/-- Horner's step on `p·Xᵏ`, reduced modulo `g` after every bit. -/
def hornerMod (g : GF2[X]) (k : ℕ) (p : GF2[X]) (b : Bool) : GF2[X] :=
  (p * X + bit b * X ^ k) %ₘ g

end

/-! ## Facts about bits and registers -/

theorem bit_false : bit false = 0 := by simp [bit]

theorem bit_true : bit true = 1 := by simp [bit]

theorem bit_xor (a b : Bool) : bit (a ^^ b) = bit a + bit b := by
  simp only [bit, ← C_add]
  congr 1
  cases a <;> cases b <;> decide

theorem char_two : (2 : GF2[X]) = 0 := CharTwo.two_eq_zero

theorem coeff_toPoly (r : BitVec k) (n : ℕ) :
    (toPoly r).coeff n = if r.getLsbD n then 1 else 0 := by
  simp only [toPoly, bit, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq,
    Finset.mem_range]
  by_cases h : n < k
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge r n (by omega)]

/-- `toPoly` forgets nothing. -/
theorem toPoly_injective : Function.Injective (toPoly : BitVec k → GF2[X]) := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have hi := congrArg (·.coeff i) h
  simp only [coeff_toPoly] at hi
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all

theorem toPoly_zero : toPoly (0 : BitVec k) = 0 := by simp [toPoly, bit_false]

theorem toPoly_xor (x y : BitVec k) : toPoly (x ^^^ y) = toPoly x + toPoly y := by
  simp only [toPoly, BitVec.getLsbD_xor, bit_xor, add_mul, Finset.sum_add_distrib]

theorem degree_toPoly_lt (r : BitVec k) : (toPoly r).degree < k := by
  rw [← mem_degreeLT]
  refine Submodule.sum_mem _ fun i hi => mem_degreeLT.2 ?_
  exact (degree_C_mul_X_pow_le i _).trans_lt (by exact_mod_cast Finset.mem_range.1 hi)

/-- Shifting a register left by `s` multiplies its polynomial by `Xˢ`. The top
`s` bits fall out of the register; they are the part of degree `k` and above. -/
theorem toPoly_mul_X_pow (r : BitVec k) (hs : s ≤ k) :
    toPoly r * X ^ s = toPoly (r <<< s) + toPoly (r.extractLsb' (k - s) s) * X ^ k := by
  ext n
  simp only [coeff_add, coeff_mul_X_pow', coeff_toPoly, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb']
  by_cases h₁ : n < s
  · simp [h₁, show ¬s ≤ n by omega, show ¬k ≤ n by omega]
  by_cases h₂ : n < k
  · simp [h₁, h₂, show s ≤ n by omega, show ¬k ≤ n by omega]
  have e : k - s + (n - k) = n - s := by omega
  by_cases h₃ : n - k < s
  · simp [h₁, h₂, h₃, e, show s ≤ n by omega, show k ≤ n by omega]
  · simp [h₁, h₂, h₃, show s ≤ n by omega, show k ≤ n by omega,
      BitVec.getLsbD_of_ge r (n - s) (by omega)]

theorem toPoly_shiftLeft_one (r : BitVec k) :
    toPoly (r <<< 1) + bit r.msb * X ^ k = toPoly r * X := by
  cases k with
  | zero => simp [toPoly, BitVec.msb, bit_false]
  | succ n =>
    rw [← pow_one X, toPoly_mul_X_pow r (by omega), BitVec.msb_eq_getLsbD_last]
    simp [toPoly]

theorem gen_monic (poly : BitVec k) : (gen poly).Monic := monic_X_pow_add (degree_toPoly_lt poly)

theorem degree_gen (poly : BitVec k) : (gen poly).degree = k := by
  rw [gen, degree_add_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact degree_toPoly_lt poly

/-- A register already holds a remainder. -/
theorem toPoly_modByMonic (poly r : BitVec k) : toPoly r %ₘ gen poly = toPoly r :=
  (modByMonic_eq_self_iff (gen_monic poly)).2 (degree_gen poly ▸ degree_toPoly_lt r)

/-- Reducing before or after a Horner step gives the same remainder. -/
theorem modByMonic_mul_X_add {g : GF2[X]} (hg : g.Monic) (p c : GF2[X]) :
    (p * X + c) %ₘ g = (p %ₘ g * X + c) %ₘ g := by
  have h : p * X + c = (p %ₘ g * X + c) + g * (p /ₘ g * X) := by
    conv_lhs => rw [← modByMonic_add_div p g]
    ring
  rw [h, add_modByMonic, (modByMonic_eq_zero_iff_dvd hg).2 (dvd_mul_right _ _), add_zero]

/-! ## The laws -/

/-- **Fold fusion.** A function that commutes with each step commutes with the fold. -/
theorem foldl_fusion {f : β → α → β} {f' : γ → α → γ} {e : β} {e' : γ} (h : β → γ)
    (hseed : h e = e') (hstep : ∀ a x, h (f a x) = f' (h a) x) :
    h ∘ foldl f e = foldl f' e' := by
  funext xs
  induction xs generalizing e e' with
  | nil => exact hseed
  | cons x xs ih => exact ih (by rw [hstep, hseed])

theorem foldl_horner (p : GF2[X]) (bs : List Bool) :
    foldl horner p bs = p * X ^ bs.length + msgPoly bs := by
  induction bs generalizing p with
  | nil => simp [msgPoly]
  | cons b bs ih => simp only [List.foldl_cons, ih, horner, msgPoly, List.length_cons]; ring

/-- **Horner's rule.** One multiply-add per bit builds the message polynomial. -/
theorem horner_rule : msgPoly = foldl horner 0 := by
  funext bs
  simp [foldl_horner]

/-- **Shift fusion.** Multiplying by `Xᵏ` commutes with Horner's step. -/
theorem shift_fusion (k : ℕ) : (· * X ^ k) ∘ foldl horner 0 = foldl (hornerShift k) 0 :=
  foldl_fusion _ (zero_mul _) fun p b => by simp only [horner, hornerShift]; ring

/-- **Reduction fusion.** Reducing modulo `g` commutes with Horner's step. -/
theorem mod_fusion {g : GF2[X]} (hg : g.Monic) (k : ℕ) :
    (· %ₘ g) ∘ foldl (hornerShift k) 0 = foldl (hornerMod g k) 0 :=
  foldl_fusion _ (zero_modByMonic g) fun q b => modByMonic_mul_X_add hg q (bit b * X ^ k)

/-- One clock of the register is one reduced Horner step on its polynomial. -/
theorem toPoly_lfsrStep (poly r : BitVec k) (b : Bool) :
    toPoly (lfsrStep poly r b) = hornerMod (gen poly) k (toPoly r) b := by
  refine ((div_modByMonic_unique (bit (r.msb ^^ b)) _ (gen_monic poly) ⟨?_, ?_⟩).2).symm
  · have hs := toPoly_shiftLeft_one r
    cases hm : r.msb <;> cases b <;>
      simp only [hm, bit_false, bit_true, zero_mul, add_zero] at hs <;>
      simp only [lfsrStep, hm, gen, toPoly_xor, Bool.false_xor, Bool.true_xor, Bool.not_false,
        Bool.not_true, bit_false, bit_true, mul_zero, mul_one, zero_mul, one_mul, add_zero,
        Bool.false_eq_true, ite_true, ite_false]
    · exact hs
    · linear_combination hs + toPoly poly * char_two
    · linear_combination hs + toPoly poly * char_two
    · linear_combination hs - X ^ k * char_two
  · rw [degree_gen]
    exact degree_toPoly_lt _

/-- **Data refinement.** Reading the register as a polynomial commutes with the clock. -/
theorem refine_fusion (poly : BitVec k) :
    toPoly ∘ foldl (lfsrStep poly) 0 = foldl (hornerMod (gen poly) k) 0 :=
  foldl_fusion _ toPoly_zero (toPoly_lfsrStep poly)

/-! ## The derivation -/

/-- The LFSR computes the CRC. Horner's rule turns the spec into a loop. Fold
fusion then moves the shift, the reduction and the data refinement into it. On
the right is the state each line keeps while it streams the message. -/
theorem crc_eq_lfsr (poly : BitVec k) : crc poly = toPoly ∘ foldl (lfsrStep poly) 0 :=
  calc crc poly
      = (· %ₘ gen poly) ∘ (· * X ^ k) ∘ msgPoly          := rfl  -- the whole message
    _ = (· %ₘ gen poly) ∘ (· * X ^ k) ∘ foldl horner 0   := by rw [horner_rule]  -- n coefficients
    _ = (· %ₘ gen poly) ∘ foldl (hornerShift k) 0        := by rw [shift_fusion]  -- n + k
    _ = foldl (hornerMod (gen poly) k) 0                 := mod_fusion (gen_monic poly) k  -- k
    _ = toPoly ∘ foldl (lfsrStep poly) 0                 := (refine_fusion poly).symm  -- k bits

theorem foldl_hornerShift (k : ℕ) (p : GF2[X]) (bs : List Bool) :
    foldl (hornerShift k) p bs = p * X ^ bs.length + msgPoly bs * X ^ k := by
  induction bs generalizing p with
  | nil => simp [msgPoly]
  | cons b bs ih =>
    simp only [List.foldl_cons, ih, hornerShift, msgPoly, List.length_cons]; ring

/-- The same register, started from any value `r₀`. A reset to all ones is common. -/
theorem lfsr_from (poly r₀ : BitVec k) (bs : List Bool) :
    toPoly (foldl (lfsrStep poly) r₀ bs) =
      (toPoly r₀ * X ^ bs.length + msgPoly bs * X ^ k) %ₘ gen poly := by
  have refine := foldl_fusion (e := r₀) toPoly rfl (toPoly_lfsrStep poly)
  have reduce := foldl_fusion (f := hornerShift k) (f' := hornerMod (gen poly) k)
    (· %ₘ gen poly) (toPoly_modByMonic poly r₀)
    (fun q b => modByMonic_mul_X_add (gen_monic poly) q (bit b * X ^ k))
  rw [← foldl_hornerShift]
  exact (congrFun refine bs).trans (congrFun reduce bs).symm

/-! ## A byte at a time -/

/-- **Fold over concatenation.** Folding a flattened list folds each piece in turn. -/
theorem fold_concat (f : β → α → β) (e : β) (g : γ → List (List α)) :
    foldl f e ∘ flatten ∘ g = foldl (foldl f) e ∘ g := by
  funext x
  simp [List.foldl_flatten]

/-- **Fold–map fusion.** A map before a fold joins the fold's step. -/
theorem fold_map (f : β → α → β) (e : β) (g : γ → α) :
    foldl f e ∘ map g = foldl (fun b c => f b (g c)) e := by
  funext x
  simp [List.foldl_map]

/-- The bits of a byte, most significant first. -/
def bitsOf (x : BitVec 8) : List Bool := List.ofFn fun i : Fin 8 => x.getMsbD i

/-- The CRC of a byte string is the CRC of its bits. -/
noncomputable def crcBytes (poly : BitVec k) : List (BitVec 8) → GF2[X] :=
  crc poly ∘ flatten ∘ map bitsOf

/-- Eight clocks: one byte, bit-serially. -/
def byteStep (poly : BitVec k) (r : BitVec k) (x : BitVec 8) : BitVec k :=
  foldl (lfsrStep poly) r (bitsOf x)

/-- The table. Entry `i` is the CRC of the single byte `i`. -/
def table (poly : BitVec k) (i : BitVec 8) : BitVec k := byteStep poly 0 i

/-- Sarwate's step. The top byte of the register meets the input byte, and one
table lookup replaces eight clocks. -/
def tableStep (t : BitVec 8 → BitVec k) (r : BitVec k) (x : BitVec 8) : BitVec k :=
  (r <<< 8) ^^^ t (r.extractLsb' (k - 8) 8 ^^^ x)

theorem msgPoly_bitsOf (x : BitVec 8) : msgPoly (bitsOf x) = toPoly x := by
  simp [msgPoly, bitsOf, toPoly, Finset.sum_range_succ, List.ofFn_succ, BitVec.getMsbD_eq_getLsbD]
  ring

theorem toPoly_byteStep (poly r : BitVec k) (x : BitVec 8) :
    toPoly (byteStep poly r x) = (toPoly r * X ^ 8 + toPoly x * X ^ k) %ₘ gen poly := by
  rw [byteStep, lfsr_from, msgPoly_bitsOf]
  rfl

/-- **Sarwate's table.** Eight clocks are one lookup, because reduction modulo `g`
is linear. -/
theorem byteStep_eq_tableStep (hk : 8 ≤ k) (poly : BitVec k) :
    byteStep poly = tableStep (table poly) := by
  funext r x
  apply toPoly_injective
  calc toPoly (byteStep poly r x)
      = (toPoly r * X ^ 8 + toPoly x * X ^ k) %ₘ gen poly := toPoly_byteStep poly r x
    _ = (toPoly (r <<< 8) + (toPoly (r.extractLsb' (k - 8) 8) + toPoly x) * X ^ k) %ₘ gen poly := by
        rw [toPoly_mul_X_pow r hk]; ring_nf
    _ = toPoly (r <<< 8) + (toPoly (r.extractLsb' (k - 8) 8 ^^^ x) * X ^ k) %ₘ gen poly := by
        rw [add_modByMonic, toPoly_modByMonic, toPoly_xor]
    _ = toPoly (tableStep (table poly) r x) := by
        rw [tableStep, toPoly_xor (r <<< 8), table, toPoly_byteStep, toPoly_zero, zero_mul,
          zero_add]

/-- The CRC of a byte string, one table lookup per byte. The first step is the
whole bit-level derivation. -/
theorem crcBytes_eq_table (hk : 8 ≤ k) (poly : BitVec k) :
    crcBytes poly = toPoly ∘ foldl (tableStep (table poly)) 0 :=
  calc crcBytes poly
      = crc poly ∘ flatten ∘ map bitsOf                          := rfl
    _ = toPoly ∘ foldl (lfsrStep poly) 0 ∘ flatten ∘ map bitsOf  := by rw [crc_eq_lfsr]; rfl
    _ = toPoly ∘ foldl (foldl (lfsrStep poly)) 0 ∘ map bitsOf    := by rw [fold_concat]
    _ = toPoly ∘ foldl (byteStep poly) 0                         := by rw [fold_map]; rfl
    _ = toPoly ∘ foldl (tableStep (table poly)) 0                := by rw [byteStep_eq_tableStep hk]

/-! ## Executable instances -/

/-- The table, computed once and stored. -/
def tableVec (poly : BitVec k) : Vector (BitVec k) 256 :=
  Vector.ofFn fun i => table poly (BitVec.ofNat 8 i)

/-- A lookup in the stored table. -/
def lookup (poly : BitVec k) (i : BitVec 8) : BitVec k := (tableVec poly)[i.toNat]'i.isLt

theorem lookup_eq_table (poly : BitVec k) : lookup poly = table poly := by
  funext i
  simp [lookup, tableVec]

/-- The fast CRC: one stored-table lookup per byte. -/
def crcFast (poly : BitVec k) (bytes : List (BitVec 8)) : BitVec k :=
  foldl (tableStep (lookup poly)) 0 bytes

/-- The fast CRC is the specification. -/
theorem crcFast_correct (hk : 8 ≤ k) (poly : BitVec k) (bytes : List (BitVec 8)) :
    toPoly (crcFast poly bytes) = crcBytes poly bytes := by
  rw [crcBytes_eq_table hk, crcFast, lookup_eq_table]
  rfl

/-- The ASCII string `"123456789"`, the catalogue's test message. -/
def check : List (BitVec 8) := [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

/-- CRC-16/XMODEM. The catalogue gives `0x31C3`. No division is ever run. -/
theorem xmodem_check : crcBytes 0x1021#16 check = toPoly 0x31C3#16 := by
  rw [crcBytes_eq_table (by decide)]
  exact congrArg toPoly (by decide)

/-- CRC-8/SMBUS. The catalogue gives `0xF4`. -/
theorem smbus_check : crcBytes 0x07#8 check = toPoly 0xF4#8 := by
  rw [crcBytes_eq_table (by decide)]
  exact congrArg toPoly (by decide)

-- CRC-32/CKSUM complements the result. The catalogue gives `0x765E7680`.
#guard crcFast 0x04C11DB7#32 check ^^^ 0xFFFFFFFF#32 == 0x765E7680#32

/-! ## The RTL

`CRC/crc8.sv` updates its register bit by bit. This is
that update, transcribed, for a clock with `valid_in` high. -/

/-- The next-state logic of `crc8.sv`. -/
def crc8Next (crc : BitVec 8) (data_in : Bool) : BitVec 8 :=
  let feedback := crc[7] ^^ data_in
  BitVec.ofBool crc[6] ++ BitVec.ofBool crc[5] ++ BitVec.ofBool crc[4] ++
  BitVec.ofBool crc[3] ++ BitVec.ofBool crc[2] ++ BitVec.ofBool (crc[1] ^^ feedback) ++
  BitVec.ofBool (crc[0] ^^ feedback) ++ BitVec.ofBool feedback

/-- The RTL is the derived LFSR for `g = X⁸ + X² + X + 1`. -/
theorem crc8Next_eq_lfsrStep : crc8Next = lfsrStep 0x07#8 := by
  funext crc b
  simp only [crc8Next, lfsrStep]
  bv_decide

/-- The generator of `crc8.sv`. -/
theorem gen_crc8 : gen 0x07#8 = X ^ 8 + X ^ 2 + X + 1 := by
  simp [gen, toPoly, Finset.sum_range_succ, bit]
  ring

/-- After reset to `0xFF`, `crc8.sv` holds `(0xFF·Xⁿ + M·X⁸) mod g` for the
`n` bits `M` it has accepted. -/
theorem crc8_rtl_correct (bs : List Bool) :
    toPoly (foldl crc8Next 0xFF#8 bs) =
      (toPoly 0xFF#8 * X ^ bs.length + msgPoly bs * X ^ 8) %ₘ (X ^ 8 + X ^ 2 + X + 1) := by
  rw [crc8Next_eq_lfsrStep, lfsr_from, gen_crc8]

end BirdMeertens.CRC
