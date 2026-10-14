import LawDiagrams
import CRC

/-!
# Diagrams of the CRC derivation

`crc_eq_lfsr` derives the LFSR from the textbook CRC, and `crcBytes_eq_table`
goes on to Sarwate's table. This executable draws a law diagram for each step
and a schematic of the program at each line.

* The bit-level steps use CRC-8/SMBUS, `g = X⁸ + X² + X + 1`, the generator of
  `CRC/crc8.sv`, on the message `1011`.
* The byte-level steps use CRC-16/XMODEM, `g = X¹⁶ + X¹² + X⁵ + 1`, on the two
  bytes of `"12"`. A width of 16 shows the whole of Sarwate's step: at width 8
  its shift `r <<< 8` is always zero.

Mathlib's polynomials over GF(2) do not compute, so the diagrams model them as
bit masks, `Poly`. A `#guard` checks the model against the registers that
`lfsrStep` from `CRC.lean` computes. Registers, bytes and tables come from
`CRC.lean` itself. The LFSR's schematic is found by running `lfsrStep` on each
unit input: the step is linear, which a `#guard` checks, so its taps are the
bits each input flips.

The executable writes `CRC/diagrams/crc_*_light.svg` and
`crc_*_dark.svg`. Run it from the repository root:

    lake exe crc_diagrams
-/

namespace CrcDiagrams

open LawDiagrams
open BirdMeertens.CRC (lfsrStep bitsOf byteStep table tableStep crc8Next)
open List (map foldl flatten)

/-! ## Polynomials over GF(2), as bit masks -/

/-- A polynomial over GF(2): bit `i` of `mask` is the coefficient of `Xⁱ`. -/
structure Poly where
  mask : Nat
  deriving BEq, Inhabited

namespace Poly

instance : Add Poly := ⟨fun p q => ⟨p.mask ^^^ q.mask⟩⟩

/-- `p · Xⁿ`. -/
def shift (p : Poly) (n : Nat) : Poly := ⟨p.mask <<< n⟩

/-- A bit, as a constant polynomial. -/
def bit (b : Bool) : Poly := ⟨if b then 1 else 0⟩

/-- The remainder of `p` divided by `g`, by long division. Each round lowers the
degree, so `p`'s degree plus one rounds are enough. `g` must not be zero; every
generator `Xᵏ + poly` is nonzero, and a `#guard` checks the two used here. -/
def mod (p g : Poly) : Poly := Id.run do
  let dg := g.mask.log2
  let mut r := p.mask
  for _ in [0:p.mask.log2 + 1] do
    if r != 0 && r.log2 ≥ dg then r := r ^^^ (g.mask <<< (r.log2 - dg))
  return ⟨r⟩

/-- The polynomial a register holds: bit `i` is the coefficient of `Xⁱ`, as in `toPoly`. -/
def ofReg {k : Nat} (r : BitVec k) : Poly := ⟨r.toNat⟩

/-- The generator `Xᵏ + poly`, as in `gen`. -/
def gen {k : Nat} (poly : BitVec k) : Poly := ⟨2 ^ k + poly.toNat⟩

/-- `n` as superscript digits. -/
def sup (n : Nat) : String :=
  (toString n).map fun ch => #['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'][ch.toNat - '0'.toNat]!

/-- `Xⁿ` as text. -/
def xPow : Nat → String
  | 0 => "1"
  | 1 => "X"
  | n => s!"X{sup n}"

/-- The polynomial as text, highest power first: `X¹¹ + X⁹ + X⁸`. -/
def text (p : Poly) : String :=
  let terms := ((List.range (p.mask.log2 + 1)).reverse.filter p.mask.testBit).map xPow
  if terms.isEmpty then "0" else " + ".intercalate terms

end Poly

instance : Draw Poly := ⟨0, fun p => [(p.text, .value)]⟩

/-! ## The intermediate programs, on `Poly`

Each mirrors its namesake in `CRC.lean`. -/

def msgPoly : List Bool → Poly
  | [] => ⟨0⟩
  | b :: bs => (Poly.bit b).shift bs.length + msgPoly bs

def horner (p : Poly) (b : Bool) : Poly := p.shift 1 + Poly.bit b

def hornerShift (k : Nat) (p : Poly) (b : Bool) : Poly := p.shift 1 + (Poly.bit b).shift k

def hornerMod (g : Poly) (k : Nat) (p : Poly) (b : Bool) : Poly := (hornerShift k p b).mod g

/-- The specification: the remainder of `M·Xᵏ` divided by `g`. -/
def crc {k : Nat} (poly : BitVec k) (bs : List Bool) : Poly :=
  ((msgPoly bs).shift k).mod (Poly.gen poly)

/-! ## The examples

Every constant the diagrams write is derived from these. -/

/-- The bit-level example: CRC-8/SMBUS, the generator of `crc8.sv`, on `1011`. -/
def k8 : Nat := 8
def poly8 : BitVec k8 := BitVec.ofNat k8 0x07
def msg : List Bool := [true, false, true, true]

/-- The byte-level example: CRC-16/XMODEM on the bytes of `"12"`. -/
def k16 : Nat := 16
def poly16 : BitVec k16 := BitVec.ofNat k16 0x1021
def bytes : List (BitVec 8) := [0x31#8, 0x32#8]

/-- A register or a byte, in hexadecimal: `0x1021`. -/
def hex {k : Nat} (r : BitVec k) : String :=
  let ds := (Nat.toDigits 16 r.toNat).map Char.toUpper
  "0x" ++ String.ofList (List.replicate ((k + 3) / 4 - ds.length) '0' ++ ds)

/-- `n` as subscript digits. -/
def sub (n : Nat) : String := (toString n).map fun ch => Char.ofNat (ch.toNat - '0'.toNat + 0x2080)

/-- The two generators, and `Xᵏ` for the bit-level width, as the diagrams write them. -/
def P8 : String := hex poly8
def P16 : String := hex poly16
def X8 : String := Poly.xPow k8

/-- The top byte of a `k16`-bit register: `r₁₅…₈`. -/
def topByte : String := s!"r{sub (k16 - 1)}…{sub (k16 - 8)}"

-- Both generators are nonzero, as `Poly.mod` needs.
#guard (Poly.gen poly8).mask != 0 && (Poly.gen poly16).mask != 0

-- The names CRC-8/SMBUS and CRC-16/XMODEM are pinned by the catalogue's check
-- values on "123456789": 0xF4 and 0x31C3.
#guard foldl (tableStep (table poly8)) 0 BirdMeertens.CRC.check == BitVec.ofNat k8 0xF4
#guard foldl (tableStep (table poly16)) 0 BirdMeertens.CRC.check == BitVec.ofNat k16 0x31C3

/-- Every message of `n` bits. -/
def messages : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (messages n).flatMap fun m => [false :: m, true :: m]

-- The model agrees with `CRC.lean`: the register `lfsrStep` leaves holds the
-- specification's remainder, for every message of up to 8 bits (CRC-8) and of
-- up to 5 bits (CRC-16). That is `crc_eq_lfsr`, run.
#guard (List.range 9).all fun n => (messages n).all fun bs =>
  Poly.ofReg (foldl (lfsrStep poly8) 0 bs) == crc poly8 bs
#guard (List.range 6).all fun n => (messages n).all fun bs =>
  Poly.ofReg (foldl (lfsrStep poly16) 0 bs) == crc poly16 bs
-- And on a long message, which divides many times: the 72 bits of "123456789".
#guard Poly.ofReg (foldl (lfsrStep poly8) 0 (flatten (BirdMeertens.CRC.check.map bitsOf))) ==
    crc poly8 (flatten (BirdMeertens.CRC.check.map bitsOf)) &&
  Poly.ofReg (foldl (lfsrStep poly16) 0 (flatten (BirdMeertens.CRC.check.map bitsOf))) ==
    crc poly16 (flatten (BirdMeertens.CRC.check.map bitsOf))

/-! ## Values as text -/

/-- A register, drawn as its bits, the coefficient of `Xᵏ⁻¹` first. -/
structure Bits (k : Nat) where
  r : BitVec k

instance {k : Nat} : Draw (Bits k) :=
  ⟨0, fun ⟨r⟩ => [(String.ofList ((List.range k).reverse.map fun i => if r.getLsbD i then '1' else '0'), .value)]⟩

/-- A register or a byte, drawn in hexadecimal. -/
structure Hex (k : Nat) where
  r : BitVec k

instance {k : Nat} : Draw (Hex k) := ⟨0, fun ⟨r⟩ => [(hex r, .value)]⟩

/-- A left fold over bits, written out. A diagram prints the term and evaluates
it, so the value it shows is the value of the term it shows. -/
inductive Term where
  | seed
  | step (t : Term) (b : Bool)

/-- The term as text: `seed`, then each step written by `stepText`. -/
def Term.text (seed : String) (stepText : String → Bool → String) : Term → String
  | .seed => seed
  | .step t b => stepText (match t with | .seed => t.text seed stepText | .step .. => s!"({t.text seed stepText})") b

def Term.eval {α : Type} (e : α) (f : α → Bool → α) : Term → α
  | .seed => e
  | .step t b => f (t.eval e f) b

/-! ## The laws -/

-- The model agrees on the byte-level examples too, through the table: on the
-- two bytes drawn here, and on the catalogue's check string "123456789", whose
-- CRC-16/XMODEM is 0x31C3.
#guard Poly.ofReg (foldl (tableStep (table poly16)) 0 bytes) == crc poly16 (flatten (bytes.map bitsOf))
#guard foldl (tableStep (table poly16)) 0 BirdMeertens.CRC.check == 0x31C3#16 &&
  Poly.ofReg 0x31C3#16 == crc poly16 (flatten (BirdMeertens.CRC.check.map bitsOf))

-- Sarwate's step agrees with eight clocks on every byte, at the register the
-- table diagram starts from.
#guard (List.range 256).all fun i =>
  let r := byteStep poly16 0 (bytes.headD 0)
  byteStep poly16 r (BitVec.ofNat 8 i) == tableStep (table poly16) r (BitVec.ofNat 8 i)

def laws : List Law :=
  let g := Poly.gen poly8
  let t := msg.foldl Term.step Term.seed
  let hornerText := t.text "0" fun s b => s!"{s}·X + {if b then "1" else "0"}"
  let shiftText := t.text "0" fun s b => s!"{s}·X + {if b then X8 else "0"}"
  let reg := foldl (lfsrStep poly8) 0 msg
  let bitLists := bytes.map bitsOf
  let r₁ := byteStep poly16 0 (bytes.headD 0)
  let x := bytes.getLastD 0
  let top := r₁.extractLsb' 8 8
  let lfsrNote := "lfsrStep poly r b = if msb r ⊕ b then (r <<< 1) ⊕ poly else r <<< 1"
  [ { file := "crc_horner", name := "Horner's rule",
      statement := "msgPoly = foldl horner 0",
      start := node msg,
      before := [("msgPoly", node (msgPoly msg))],
      after := [("foldl horner 0", node2 hornerText (t.eval ⟨0⟩ horner))],
      note := ["horner p b = p·X + b"] },
    { file := "crc_shift_fusion", name := "Shift fusion",
      statement := s!"(· * {X8}) ∘ foldl horner 0 = foldl (hornerShift {k8}) 0",
      start := node msg,
      before := [("foldl horner 0", node (foldl horner ⟨0⟩ msg)),
        (s!"· * {X8}", node ((foldl horner ⟨0⟩ msg).shift k8))],
      after := [(s!"foldl (hornerShift {k8}) 0", node2 shiftText (t.eval ⟨0⟩ (hornerShift k8)))],
      note := ["hornerShift k p b = p·X + b·Xᵏ"] },
    { file := "crc_mod_fusion", name := "Reduction fusion",
      statement := s!"(· %ₘ g) ∘ foldl (hornerShift {k8}) 0 = foldl (hornerMod g {k8}) 0",
      start := node msg,
      before := [(s!"foldl (hornerShift {k8}) 0", node (foldl (hornerShift k8) ⟨0⟩ msg)),
        ("· %ₘ g", node ((foldl (hornerShift k8) ⟨0⟩ msg).mod g))],
      after := [(s!"foldl (hornerMod g {k8}) 0", node (foldl (hornerMod g k8) ⟨0⟩ msg))],
      note := [s!"g = {g.text}", "hornerMod g k p b = (p·X + b·Xᵏ) %ₘ g"] },
    { file := "crc_refine_fusion", name := "Data refinement",
      statement := s!"foldl (hornerMod g {k8}) 0 = toPoly ∘ foldl (lfsrStep {P8}) 0",
      start := node msg,
      before := [(s!"foldl (hornerMod g {k8}) 0", node (foldl (hornerMod g k8) ⟨0⟩ msg))],
      after := [(s!"foldl (lfsrStep {P8}) 0", node (Bits.mk reg)), ("toPoly", node (Poly.ofReg reg))],
      note := [lfsrNote, s!"toPoly r = Σ rᵢ·Xⁱ, so bit {k8 - 1}, on the left, is the coefficient of {Poly.xPow (k8 - 1)}"] },
    { file := "crc_fold_concat", name := "Fold over concatenation",
      statement := "foldl f e ∘ flatten = foldl (foldl f) e",
      start := node bitLists,
      before := [("flatten", node (flatten bitLists)),
        (s!"foldl (lfsrStep {P16}) 0", node (Hex.mk (foldl (lfsrStep poly16) 0 (flatten bitLists))))],
      after := [(s!"foldl (foldl (lfsrStep {P16})) 0",
        node (Hex.mk (foldl (foldl (lfsrStep poly16)) 0 bitLists)))],
      note := [s!"f = lfsrStep {P16} and e = 0, for CRC-16/XMODEM"],
      arc := true },
    { file := "crc_fold_map", name := "Fold–map fusion",
      statement := "foldl (foldl f) e ∘ map bitsOf = foldl byteStep e",
      start := node (bytes.map Hex.mk),
      before := [("map bitsOf", node bitLists),
        (s!"foldl (foldl (lfsrStep {P16})) 0", node (Hex.mk (foldl (foldl (lfsrStep poly16)) 0 bitLists)))],
      after := [(s!"foldl (byteStep {P16}) 0", node (Hex.mk (foldl (byteStep poly16) 0 bytes)))],
      note := ["byteStep poly r x = foldl (lfsrStep poly) r (bitsOf x)",
        "bitsOf x lists the bits of x, most significant first"],
      arc := true },
    { file := "crc_table", name := "Sarwate's table",
      statement := "byteStep poly = tableStep (table poly), for a width of 8 or more",
      start := node (Hex.mk r₁, Hex.mk x),
      before := [(s!"byteStep {P16}", node (Hex.mk (byteStep poly16 r₁ x)))],
      after := [(s!"tableStep (table {P16})",
        [[(s!"{hex (r₁ <<< 8)} ⊕ table ({hex top} ⊕ {hex x})", .value)],
         [("= ", .label), (s!"{hex (r₁ <<< 8)} ⊕ {hex (table poly16 (top ^^^ x))}", .value)],
         ("= ", .label) :: Draw.spans (Hex.mk (tableStep (table poly16) r₁ x))])],
      note := [s!"the start is (r, x): the register after the byte {hex (bytes.headD 0)}, and the byte {hex x}",
        s!"tableStep t r x = (r <<< 8) ⊕ t ({topByte} ⊕ x)",
        "table poly i = byteStep poly 0 i, the CRC of the single byte i"] } ]

-- Shift fusion ends at two results written differently, side by side, which
-- is the case `chain` leaves room for: it lays out without a fault.
#guard (laws.find? (·.file == "crc_shift_fusion")).any fun l => (layout l).any (·.fault.isNone)

/-! ## Finding the LFSR in `lfsrStep`

`lfsrStep poly` is linear in the register and the message bit together. So its
behaviour is fixed by what it does to each unit input, and the drawing can be
read off those. -/

/-- The register with only bit `j` set. -/
def unit (k j : Nat) : BitVec k := BitVec.ofNat k (2 ^ j)

/-- A step is linear if it maps every input to the sum of what it maps that
input's unit parts to. -/
def linear {k : Nat} (step : BitVec k → Bool → BitVec k) : Bool :=
  (List.range (2 ^ (k + 1))).all fun m =>
    let r := BitVec.ofNat k m
    let b := m / 2 ^ k == 1
    let parts := ((List.range k).filter (r.getLsbD ·)).map (fun j => step (unit k j) false) ++
      (if b then [step 0 true] else [])
    step r b == parts.foldl (· ^^^ ·) 0

/-- The taps of a Galois LFSR: `some taps` if, on unit inputs, the step shifts
each bit up by one and feeds the top bit and the message bit back into the bits
of `taps`. Then `rᵢ' = rᵢ₋₁ ⊕ (tapᵢ ∧ (r_top ⊕ b))`. -/
def galoisTaps {k : Nat} (step : BitVec k → Bool → BitVec k) : Option (BitVec k) :=
  let taps := step 0 true
  let shifts := (List.range (k - 1)).all fun j => step (unit k j) false == unit k (j + 1)
  if step 0 false == 0 && shifts && step (unit k (k - 1)) false == taps then some taps else none

#guard linear (lfsrStep poly8) && galoisTaps (lfsrStep poly8) == some poly8
-- The width-16 step has the same shape. Its linearity is checked only on a
-- sample, every register with one or two bits set with each message bit,
-- because an exhaustive check of 2¹⁷ inputs would slow every build. No
-- schematic is read off the width-16 taps: only the 8-bit LFSR is, and its
-- linearity is checked exhaustively above. The width-16 diagrams rest on
-- `crcBytes_eq_table`, proved in `CRC.lean`, not on this guard.
#guard galoisTaps (lfsrStep poly16) == some poly16 &&
  ((List.range k16).flatMap fun i => (List.range k16).map fun j => unit k16 i ^^^ unit k16 j).all fun r =>
    [false, true].all fun b =>
      lfsrStep poly16 r b == ((List.range k16).filter (r.getLsbD ·)).foldl
        (fun acc j => acc ^^^ lfsrStep poly16 (unit k16 j) false) (if b then lfsrStep poly16 0 true else 0)
-- `lfsrSch` draws the feedback into bit 0, so it needs bit 0 tapped. Every
-- CRC generator has a constant term, and these do.
#guard poly8.getLsbD 0 && poly16.getLsbD 0
-- `crc8.sv` has the same taps, as `crc8Next_eq_lfsrStep` proves.
#guard linear crc8Next && galoisTaps crc8Next == some poly8

/-! ## Schematics -/

/-- The kinds of block in a schematic. -/
inductive Shape where
  /-- A function: a box with its name. -/
  | box
  /-- A register: a box with a clock mark. -/
  | reg
  | xor
  /-- An input or an output: a name, with no outline. -/
  | io
  deriving BEq, Inhabited

/-- A block, centred on `(x, y)`. -/
structure Blk where
  id : String
  shape : Shape
  x : Float
  y : Float
  lines : List String := []
  deriving Inhabited

/-- Half the width and height of a block. -/
def Blk.half (b : Blk) : Float × Float :=
  let w := b.lines.foldl (fun m s => max m (textW s)) 0
  match b.shape with
  | .xor => (9, 9)
  | .io => (w / 2 + 2, 9)
  | _ => (max (w / 2 + 10) 20, 9 * b.lines.length.toFloat + 5)

def Blk.left (b : Blk) : Float × Float := (b.x - b.half.1, b.y)
def Blk.right (b : Blk) : Float × Float := (b.x + b.half.1, b.y)
def Blk.top (b : Blk) : Float × Float := (b.x, b.y - b.half.2)
def Blk.bottom (b : Blk) : Float × Float := (b.x, b.y + b.half.2)

/-- A wire: a polyline, with an arrowhead at its end unless it ends on a junction. -/
structure Wire where
  pts : List (Float × Float)
  /-- The blocks at its ends, which it may touch. -/
  ends : List String := []
  arrow : Bool := true
  /-- A junction dot where the wire leaves another. -/
  dot : Bool := false
  label : Option (String × Float × Float) := none
  deriving Inhabited

/-- A schematic: blocks, wires, free labels, and the lines of its legend. -/
structure Sch where
  file : String
  name : String
  /-- The line of the `calc` block it draws. -/
  line : String
  blks : List Blk
  wires : List Wire
  /-- Labels that belong to no block: their centre and text. -/
  texts : List (Float × Float × String) := []
  legend : List String
  w : Float
  h : Float
  deriving Inhabited

/-- The row of most blocks. -/
def rowY : Float := top0 + 48

def io (id s : String) : Blk := ⟨id, .io, 0, 0, [s]⟩
def box (id : String) (ls : List String) : Blk := ⟨id, .box, 0, 0, ls⟩
def reg (id : String) (ls : List String) : Blk := ⟨id, .reg, 0, 0, ls⟩

def find (bs : List Blk) (id : String) : Blk := (bs.find? (·.id == id)).getD default

/-- Lay out stages left to right on row `y`. Each stage is a block, and the
label of the wire into it; the gap fits the label. -/
def pipeline (x₀ y : Float) (stages : List (Blk × String)) : List Blk × List Wire := Id.run do
  let mut blks : Array Blk := #[]
  let mut wires : Array Wire := #[]
  for (b, lab) in stages do
    let b := { b with y }
    match blks.back? with
    | none => blks := blks.push { b with x := x₀ + b.half.1 }
    | some p =>
      let gap := max 44 (textW lab + 24)
      let nb : Blk := { b with x := p.x + p.half.1 + gap + b.half.1 }
      blks := blks.push nb
      wires := wires.push
        { pts := [p.right, nb.left], ends := [p.id, nb.id],
          label := if lab.isEmpty then none
            else some (lab, (p.x + p.half.1 + nb.x - nb.half.1) / 2, y - 9) }
  return (blks.toList, wires.toList)

/-- The page width that a schematic's blocks need. -/
def widthOf (bs : List Blk) : Float := bs.foldl (fun m b => max m (b.x + b.half.1)) 0 + M

/-- A fold as a machine. `input` stages bring each element to `step`, and the
register keeps the step's result for the next element. After the last element,
the `post` stages read the register. -/
def machine (file name line : String) (input : List (Blk × String)) (step : List String)
    (stepLabel : String) (state : List String) (post : List (Blk × String))
    (legend : List String) : Sch :=
  let stages := input ++ [(box "step" step, stepLabel), (reg "reg" state, "")] ++ post
  let (blks, wires) := pipeline (M + 4) rowY stages
  let s := find blks "step"
  let r := find blks "reg"
  -- The feedback leaves the register's output just right of it, and enters the step from below.
  let jx := r.x + r.half.1 + 14
  let yb := rowY + max s.half.2 r.half.2 + 22
  let fb : Wire := { pts := [(jx, rowY), (jx, yb), (s.x, yb), s.bottom], ends := [s.id], dot := true }
  { file, name, line, blks, wires := wires ++ [fb], legend, w := widthOf blks, h := yb + 14 }

/-- The specification, as a pipeline over the whole message. -/
def specSch : Sch :=
  let (blks, wires) := pipeline (M + 4) rowY
    [(io "m" "M", ""), (box "msg" ["msgPoly"], "n bits"), (box "shift" [s!"· * {X8}"], "n coefficients"),
     (box "mod" ["· %ₘ g"], s!"n + {k8}"), (io "out" "CRC", toString k8)]
  { file := "crc_circuit_spec", name := "The specification: the whole message at once",
    line := s!"(· %ₘ g) ∘ (· * {X8}) ∘ msgPoly", blks, wires,
    legend := ["The label on each wire counts the coefficients it carries.",
      "Nothing is computed until the whole message has arrived."],
    w := widthOf blks, h := rowY + 34 }

/-- The Galois LFSR with the given taps, as found in `lfsrStep`: `k` register
bits in a row, an XOR before each tapped bit, and the feedback `r_top ⊕ b`
returning along the bottom. Under each bit is the coefficient it holds. The
register needs at least one bit, which the caller proves. -/
def lfsrSch (file name line : String) {k : Nat} (taps : BitVec k) (legend : List String)
    (_ : 0 < k := by decide) : Sch := Id.run do
  let dx : Float := 92
  let x₀ := M + 50
  let yf := rowY + 30
  let yb := yf + 62
  let mut blks : Array Blk := #[]
  let mut wires : Array Wire := #[]
  for i in [0:k] do
    blks := blks.push ⟨s!"r{i}", .reg, x₀ + dx * i.toFloat, yf, [s!"r{sub i}"]⟩
  -- Between bit i - 1 and bit i: an XOR with the feedback if bit i is tapped, else a wire.
  for i in [1:k] do
    let p := blks[i - 1]!
    let q := blks[i]!
    if taps.getLsbD i then
      let xg : Blk := ⟨s!"x{i}", .xor, (p.x + q.x) / 2, yf, []⟩
      blks := blks.push xg
      wires := wires.push { pts := [p.right, xg.left], ends := [p.id, xg.id] }
      wires := wires.push { pts := [xg.right, q.left], ends := [xg.id, q.id] }
      wires := wires.push { pts := [(xg.x, yb), xg.bottom], ends := [xg.id], dot := true }
    else
      wires := wires.push { pts := [p.right, q.left], ends := [p.id, q.id] }
  let topR := blks[k - 1]!
  let fb : Blk := ⟨"fb", .xor, topR.x + dx * 0.75, yf, []⟩
  let b : Blk := ⟨"b", .io, fb.x, yf - 48, ["b"]⟩
  blks := blks.push fb |>.push b
  wires := wires.push { pts := [topR.right, fb.left], ends := [topR.id, fb.id] }
  wires := wires.push { pts := [b.bottom, fb.top], ends := [b.id, fb.id] }
  let r0 := blks[0]!
  let xin := r0.x - r0.half.1 - 24
  wires := wires.push
    { pts := [fb.bottom, (fb.x, yb), (xin, yb)] ++ (if taps.getLsbD 0 then [(xin, yf), r0.left] else []),
      ends := [fb.id, r0.id], arrow := taps.getLsbD 0,
      label := some (s!"feedback: r{sub (k - 1)} ⊕ b", (r0.x + topR.x) / 2, yb + 18) }
  let texts := (List.range k).map fun i => (x₀ + dx * i.toFloat, yf + 34, Poly.xPow i)
  return ({
    file, name, line, blks := blks.toList, wires := wires.toList, texts, legend,
    w := fb.x + 9 + M, h := yb + 30 } : Sch)

/-- `byteStep` unrolled: the register feeds eight `lfsrStep` stages in a row, one
for each bit of the byte, most significant first, and takes the last one's
result at the next clock. The stages come from `bitsOf`. -/
def byteStepSch : Sch := Id.run do
  let n := (bitsOf 0).length
  let stages : List (Blk × String) := (reg "reg" ["r", s!"{k16} bits"], "") ::
    (List.range n).map fun i => (box s!"s{i}" ["step"], "")
  let (blks, wires) := pipeline (M + 4) (rowY + 24) stages
  let ins : List Blk := (List.range n).map fun i =>
    let s := find blks s!"s{i}"
    ⟨s!"x{i}", .io, s.x, rowY - 24, [s!"x{sub (n - 1 - i)}"]⟩
  let inWires := (List.range n).map fun i =>
    let s := find blks s!"s{i}"
    let x := find ins s!"x{i}"
    ({ pts := [x.bottom, s.top], ends := [x.id, s.id] } : Wire)
  let r := find blks "reg"
  let last := find blks s!"s{n - 1}"
  let yb := rowY + 24 + r.half.2 + 24
  let back : Wire := { pts := [last.right, (last.x + last.half.1 + 16, rowY + 24),
    (last.x + last.half.1 + 16, yb), (r.x, yb), r.bottom], ends := [last.id, r.id] }
  return ({
    file := "crc_circuit_bytestep", name := "byteStep: eight clocks in one",
    line := s!"toPoly ∘ foldl (byteStep {P16}) 0", blks := blks ++ ins, wires := wires ++ inWires ++ [back],
    legend := [s!"step is lfsrStep {P16}. Stage i takes bit i of bitsOf x, the most significant first.",
      "The register now changes once a byte, not once a bit."],
    w := last.x + last.half.1 + 16 + M, h := yb + 14 } : Sch)

/-- Sarwate's step: the top byte of the register meets the input byte, one table
lookup replaces eight clocks, and the rest of the register shifts up a byte. -/
def tableSch : Sch :=
  let yU := rowY
  let yL := rowY + 76
  let r : Blk := ⟨"reg", .reg, M + 40, (yU + yL) / 2, ["r", s!"{k16} bits"]⟩
  let sh : Blk := ⟨"sh", .box, M + 190, yU, ["r <<< 8"]⟩
  let tb : Blk := ⟨"tb", .box, M + 190, yL, [topByte]⟩
  let x1 : Blk := ⟨"x1", .xor, M + 330, yL, []⟩
  let xi : Blk := ⟨"xi", .io, M + 330, yL + 46, ["x"]⟩
  let tab : Blk := ⟨"tab", .box, M + 470, yL, [s!"table {P16}", "256 entries"]⟩
  let x2 : Blk := ⟨"x2", .xor, M + 600, yU, []⟩
  let jx := r.x + r.half.1 + 22
  let yTop := yU - 36
  let blks := [r, sh, tb, x1, xi, tab, x2]
  let wires : List Wire :=
    [ { pts := [r.right, (jx, r.y)], ends := [r.id], arrow := false },
      { pts := [(jx, r.y), (jx, yU), sh.left], ends := [sh.id], dot := true },
      { pts := [(jx, r.y), (jx, yL), tb.left], ends := [tb.id], dot := true },
      { pts := [tb.right, x1.left], ends := [tb.id, x1.id], label := some ("top byte", (tb.x + tb.half.1 + x1.x - 9) / 2, yL - 9) },
      { pts := [xi.top, x1.bottom], ends := [xi.id, x1.id] },
      { pts := [x1.right, tab.left], ends := [x1.id, tab.id], label := some ("index", (x1.x + 9 + tab.x - tab.half.1) / 2, yL - 9) },
      { pts := [sh.right, x2.left], ends := [sh.id, x2.id] },
      { pts := [tab.right, (x2.x, yL), x2.bottom], ends := [tab.id, x2.id] },
      { pts := [x2.right, (x2.x + 24, yU), (x2.x + 24, yTop), (r.x, yTop), r.top], ends := [x2.id, r.id] } ]
  { file := "crc_circuit_table", name := "Sarwate's table: one lookup a byte",
    line := s!"toPoly ∘ foldl (tableStep (table {P16})) 0", blks, wires,
    legend := [s!"table i = byteStep {P16} 0 i, computed once: 256 entries of {k16} bits.",
      "Reduction modulo g is linear, which is why one lookup can stand for eight clocks."],
    w := x2.x + 24 + M + 10, h := yL + 46 + 14 }

/-- The schematics, in the order of the two `calc` blocks. -/
def schematics : List Sch :=
  let taps := (galoisTaps (lfsrStep poly8)).getD 0
  [ specSch,
    machine "crc_circuit_horner" "Horner's rule: a loop, but its state grows"
      s!"(· %ₘ g) ∘ (· * {X8}) ∘ foldl horner 0"
      [(io "b" "b", "")] ["p·X + b"] "" ["p", "n coefficients"]
      [(box "shift" [s!"· * {X8}"], "after the last bit"), (box "mod" ["· %ₘ g"], s!"n + {k8}"),
       (io "out" "CRC", toString k8)]
      ["Each message bit b enters the step, and the register keeps the result.",
       "After the last bit, p is the whole message polynomial."],
    machine "crc_circuit_shift" "Shift fusion: the shift moves into the loop"
      s!"(· %ₘ g) ∘ foldl (hornerShift {k8}) 0"
      [(io "b" "b", "")] [s!"p·X + b·{X8}"] "" ["p", s!"n + {k8} coefficients"]
      [(box "mod" ["· %ₘ g"], "after the last bit"), (io "out" "CRC", toString k8)]
      [s!"Each bit enters at {X8}, so the register grows to n + {k8} coefficients."],
    machine "crc_circuit_mod" s!"Reduction fusion: the state stays at {k8} coefficients"
      s!"foldl (hornerMod g {k8}) 0"
      [(io "b" "b", "")] [s!"(p·X + b·{X8}) %ₘ g"] "" ["p", s!"{k8} coefficients"]
      [(io "out" "CRC", "after the last bit")]
      [s!"Reducing after every bit keeps p below degree {k8}."],
    lfsrSch "crc_circuit_lfsr" s!"Data refinement: an {k8}-bit LFSR, which is crc8.sv"
      s!"toPoly ∘ foldl (lfsrStep {P8}) 0" taps
      [s!"The taps are the bits of {P8}, found by running lfsrStep on each unit input.",
       "Bit rᵢ holds the coefficient of Xⁱ. Each clock shifts the register up one bit.",
       "crc8.sv has exactly these gates: crc8Next_eq_lfsrStep proves it."],
    machine "crc_circuit_serial" "A byte at a time, through the bit-serial LFSR"
      s!"toPoly ∘ foldl (lfsrStep {P16}) 0 ∘ flatten ∘ map bitsOf"
      [(io "x" "x", ""), (box "bits" ["bitsOf"], "a byte")] [s!"lfsrStep {P16}"] "b"
      ["r", s!"{k16} bits"] [(box "poly" ["toPoly"], "after the last byte"), (io "out" "CRC", "")]
      ["bitsOf turns each byte into eight bits, most significant first: eight clocks a byte.",
       s!"Folding over the bytes in turn, as foldl (foldl (lfsrStep {P16})) 0, changes nothing here."],
    byteStepSch,
    tableSch ]

/-! ## Checking and drawing a schematic -/

/-- Every piece of text in a schematic, with what it covers. -/
def Sch.textRects (s : Sch) : List (String × Rect) :=
  s.blks.flatMap (fun b =>
    let n := b.lines.length.toFloat
    (b.lines.zip (List.range b.lines.length)).map fun (l, i) =>
      (l, textRect b.x (b.y + 4.5 + 18 * (i.toFloat - (n - 1) / 2)) l "middle")) ++
  s.wires.filterMap (fun w => w.label.map fun (l, x, y) => (l, textRect x y l "middle")) ++
  s.texts.map fun (x, y, l) => (l, textRect x (y + 4.5) l "middle")

/-- Points at most a few pixels apart along every wire. -/
def Wire.points (w : Wire) : List (Float × Float) :=
  (w.pts.zip (w.pts.drop 1)).flatMap fun ((x₀, y₀), (x₁, y₁)) =>
    (List.range 41).map fun i => let t := i.toFloat / 40; (x₀ + (x₁ - x₀) * t, y₀ + (y₁ - y₀) * t)

/-- A fault in a schematic: a wire with a segment of length 0, which has no
direction for its arrowhead; a text off the page or over another; a label on a
block; or a wire through a block that is not one of its ends, or through a text. -/
def Sch.fault (s : Sch) : Option String :=
  let ts := s.textRects
  let off := ts.find? fun (_, r) => r.l < 0 || r.r > s.w || r.t < top0 - 28 || r.b > s.h
  let clash := (List.range ts.length).findSome? fun i => (List.range i).findSome? fun j =>
    if (ts.getD i default).2.meets (ts.getD j default).2 then
      some s!"{(ts.getD j default).1} overlaps {(ts.getD i default).1}" else none
  let labels : List (String × Float × Float) :=
    s.wires.filterMap (fun (w : Wire) => w.label) ++ s.texts.map fun (x, y, l) => (l, x, y + 4.5)
  let onBlk := labels.findSome? fun (l, x, y) =>
    let r := textRect x y l "middle"
    (s.blks.find? fun (b : Blk) => let (hw, hh) := b.half
      r.l < b.x + hw && b.x - hw < r.r && r.t < b.y + hh && b.y - hh < r.b).map
      fun (b : Blk) => s!"{l} overlaps the block {b.id}"
  let degenerate := s.wires.any fun w => w.pts.length < 2 ||
    (w.pts.zip (w.pts.drop 1)).any fun ((x₀, y₀), (x₁, y₁)) => x₀ == x₁ && y₀ == y₁
  let hit := s.wires.findSome? fun w =>
    let inBlk := s.blks.find? fun b =>
      !(w.ends.contains b.id) && let (hw, hh) := b.half
        w.points.any fun (x, y) => (x - b.x).abs < hw + 2 && (y - b.y).abs < hh + 2
    -- A wire may touch its own label: that rectangle, not any text that reads the same.
    let own := w.label.map fun (l, x, y) => textRect x y l "middle"
    let isOwn (rc : Rect) : Bool := match own with
      | some o => o.l == rc.l && o.t == rc.t && o.r == rc.r && o.b == rc.b
      | none => false
    let inText := ts.find? fun (_, rc) => !isOwn rc && w.points.any fun (x, y) => rc.contains x y
    match inBlk, inText with
    | some b, _ => some s!"a wire crosses the block {b.id}"
    | none, some (l, _) => some s!"a wire crosses {l}"
    | none, none => none
  if degenerate then some "a wire has a segment of length 0" else
  match off with
  | some (l, _) => some s!"{l} is off the page"
  | none => clash.orElse fun _ => onBlk.orElse fun _ => hit

/-! The checks catch what they are meant to. -/

/-- One box on a page 300 px square, with the given wires and free labels. -/
def testSch (wires : List Wire) (texts : List (Float × Float × String) := []) : Sch :=
  { file := "", name := "", line := "", blks := [⟨"a", .box, 150, 150, ["box"]⟩],
    wires, texts, legend := [], w := 300, h := 300 }

#guard (testSch [{ pts := [(20, 150), (100, 150)] }]).fault.isNone
#guard (testSch [{ pts := [(20, 150), (280, 150)] }]).fault == some "a wire crosses the block a"
#guard (testSch [] [(150, 166, "label")]).fault == some "label overlaps the block a"
-- A wire may touch its own label, but not another text that reads the same.
#guard (testSch [{ pts := [(20, 250), (280, 250)], label := some ("dup", 60, 241) }]
  [(200, 248, "dup")]).fault == some "a wire crosses dup"
#guard (testSch [] [(4, 200, "a long label")]).fault == some "a long label is off the page"
#guard (testSch [{ pts := [(20, 150), (60, 150), (60, 150)] }]).fault == some "a wire has a segment of length 0"

def blkSvg (th : Theme) (b : Blk) : String :=
  let (hw, hh) := b.half
  let n := b.lines.length.toFloat
  let labels := String.join ((b.lines.zip (List.range b.lines.length)).map fun (l, i) =>
    textLine th b.x (b.y + 4.5 + 18 * (i.toFloat - (n - 1) / 2)) [(l, .value)])
  match b.shape with
  | .xor =>
    s!"<circle cx=\"{num b.x}\" cy=\"{num b.y}\" r=\"9\" fill=\"{th.surface}\" stroke=\"{th.ink2}\" stroke-width=\"1.5\"/>\n" ++
    s!"<path d=\"M {num (b.x - 9)} {num b.y} H {num (b.x + 9)} M {num b.x} {num (b.y - 9)} V {num (b.y + 9)}\" stroke=\"{th.ink2}\" stroke-width=\"1.5\"/>\n"
  | .io => labels
  | .box =>
    s!"<rect x=\"{num (b.x - hw)}\" y=\"{num (b.y - hh)}\" width=\"{num (2 * hw)}\" height=\"{num (2 * hh)}\" rx=\"3\" fill=\"{th.surface}\" stroke=\"{th.ink2}\" stroke-width=\"1.5\"/>\n" ++ labels
  | .reg =>
    s!"<rect x=\"{num (b.x - hw)}\" y=\"{num (b.y - hh)}\" width=\"{num (2 * hw)}\" height=\"{num (2 * hh)}\" rx=\"1\" fill=\"{th.surface}\" stroke=\"{th.ink}\" stroke-width=\"2\"/>\n" ++
    s!"<path d=\"M {num (b.x - 6)} {num (b.y + hh)} L {num b.x} {num (b.y + hh - 6)} L {num (b.x + 6)} {num (b.y + hh)}\" fill=\"none\" stroke=\"{th.ink}\" stroke-width=\"1.25\"/>\n" ++ labels

def wireSvg (th : Theme) (w : Wire) : String :=
  let d := " ".intercalate (w.pts.map fun (x, y) => s!"{num x},{num y}")
  let line := s!"<polyline points=\"{d}\" fill=\"none\" stroke=\"{th.ink2}\" stroke-width=\"1.25\"/>\n"
  let head := match w.pts.reverse with
    | (x₁, y₁) :: (x₀, y₀) :: _ =>
      if !w.arrow then "" else
      let len := Float.sqrt ((x₁ - x₀) * (x₁ - x₀) + (y₁ - y₀) * (y₁ - y₀))
      let (ux, uy) := ((x₁ - x₀) / len, (y₁ - y₀) / len)
      s!"<polygon points=\"{num x₁},{num y₁} {num (x₁ - 8 * ux + 3.5 * uy)},{num (y₁ - 8 * uy - 3.5 * ux)} {num (x₁ - 8 * ux - 3.5 * uy)},{num (y₁ - 8 * uy + 3.5 * ux)}\" fill=\"{th.ink2}\"/>\n"
    | _ => ""
  let dot := match w.pts.head? with
    | some (x, y) => if w.dot then s!"<circle cx=\"{num x}\" cy=\"{num y}\" r=\"3\" fill=\"{th.ink2}\"/>\n" else ""
    | none => ""
  let label := match w.label with
    | some (l, x, y) => textLine th x y [(l, .label)]
    | none => ""
  line ++ head ++ dot ++ label

def legendRowH : Float := 20

def Sch.svg (s : Sch) (th : Theme) : String := Id.run do
  let legendW := s.legend.foldl (fun m l => max m (textW l)) 0
  let W := max s.w (max (2 * M + legendW + 24) (2 * M + max (textW s.line) (s.name.length.toFloat * 9.5)))
  let top := s.h + 18
  let H := top + 16 + legendRowH * s.legend.length.toFloat + M
  let desc := s!"{s.name}. The circuit of the line {s.line}. " ++ " ".intercalate s.legend
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{num W}\" height=\"{num H}\" viewBox=\"0 0 {num W} {num H}\" font-family=\"{sans}\" role=\"img\" aria-labelledby=\"title desc\">\n"
  out := out ++ s!"<title id=\"title\">{esc s.name}</title>\n<desc id=\"desc\">{esc desc}</desc>\n"
  out := out ++ s!"<rect width=\"100%\" height=\"100%\" fill=\"{th.surface}\"/>\n"
  out := out ++ s!"<text x=\"{num M}\" y=\"36\" font-size=\"16\" font-weight=\"600\" fill=\"{th.ink}\">{esc s.name}</text>\n"
  out := out ++ s!"<g font-family=\"{mono}\" font-size=\"13\">\n"
  out := out ++ textLine th M 60 [(s.line, .label)] "start"
  for w in s.wires do
    out := out ++ wireSvg th w
  for b in s.blks do
    out := out ++ blkSvg th b
  for (x, y, l) in s.texts do
    out := out ++ textLine th x (y + 4.5) [(l, .label)]
  if !s.legend.isEmpty then
    out := out ++ s!"<rect x=\"{num M}\" y=\"{num top}\" width=\"{num (W - 2 * M)}\" height=\"{num (16 + legendRowH * s.legend.length.toFloat)}\" rx=\"4\" fill=\"{th.note}\" stroke=\"{th.noteEdge}\"/>\n"
    for i in [0:s.legend.length] do
      out := out ++ textLine th (M + 12) (top + 22 + legendRowH * i.toFloat) [(s.legend.getD i "", .label)] "start"
  out := out ++ "</g>\n</svg>\n"
  return out

def Sch.drawing (s : Sch) : Drawing := do
  if let some f := s.fault then throw s!"{s.name}: {f}"
  return s.svg

def main : IO UInt32 :=
  writeAll "crc_diagrams" "CRC/diagrams"
    (laws.map (fun l => (l.file, l.drawing)) ++ schematics.map (fun s => (s.file, s.drawing)))

end CrcDiagrams

def main : IO UInt32 := CrcDiagrams.main
