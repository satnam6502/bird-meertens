import LawDiagrams
import Adder

/-!
# Diagrams of the refinement from ripple-carry to carry-lookahead

`refine_cla_from_ripple_carry` turns a row of full adders into Sklansky's
carry-lookahead adder in six steps. This executable draws two kinds of
diagram for them.

* A law diagram for each step, like the Kadane ones: the law applied to three
  columns, with the line before the step on the left and the line after it on
  the right. The values come from the definitions in `Adder.lean`.
* A schematic of the circuit at each line of the `calc` block, for seven
  columns. The schematics come from running `row`, `scanl`, `scan1` and
  `prefixNet` themselves on symbolic wires, so each one shows the network that
  its line builds. Each schematic is also evaluated, cell by cell, with the
  functions of `Adder.lean`, and must add on every input.

The executable writes `Adder/diagrams/adder_*_light.svg` and
`adder_*_dark.svg`. Run it from the repository root:

    lake exe adder_diagrams
-/

namespace AdderDiagrams

open LawDiagrams
open BirdMeertens BirdMeertens.Adder
open List (map foldl)

local infixl:70 " ⊛ " => dot

/-- `n` as subscript digits. -/
def sub (n : Nat) : String := (toString n).map fun ch => Char.ofNat (ch.toNat - '0'.toNat + 0x2080)

/-! ## The laws -/

/-- A term of a prefix network on inputs `q₀, q₁, …`. -/
inductive PTm where
  | q (i : Nat)
  | op (a b : PTm)
  deriving BEq, Inhabited

/-- The term as text, with every compound operand bracketed. -/
def PTm.text : PTm → String
  | .q i => s!"q{sub i}"
  | .op a b =>
    let w (t : PTm) (s : String) := match t with | .q _ => s | .op .. => s!"({s})"
    s!"{w a a.text} ⊛ {w b b.text}"

/-- The term's value, given the values of the inputs. `none` if it names an
input that is not there. -/
def PTm.eval (qs : List (Bool × Bool)) : PTm → Option (Bool × Bool)
  | .q i => qs[i]?
  | .op a b => return (← a.eval qs) ⊛ (← b.eval qs)

/-- The carry in of the example. -/
def c : Bool := true

/-- The columns of the example, least significant first: `5 + 4 + 1 = 10`. The
first column propagates the carry in, the second kills it, and the third
generates a carry out. -/
def xs : List Col := [(true, false), (false, false), (true, true)]

/-- The inputs of the prefix network, and the same inputs as symbols. -/
def qs : List (Bool × Bool) := (c, false) :: map gp xs
def syms : List PTm := (List.range qs.length).map PTm.q

-- The written-out terms evaluate to what the scan and the network compute.
#guard (scan1 PTm.op syms).mapM (PTm.eval qs) == some (scan1 (· ⊛ ·) qs)
#guard (prefixNet PTm.op syms).mapM (PTm.eval qs) == some (prefixNet (· ⊛ ·) qs)

/-- One diagram for each step of `refine_cla_from_ripple_carry` that applies a
law, in order. The last step, the definition of `cla`, only names the circuit. -/
def laws : List Law :=
  let gps := map gp xs
  let pairs := scanl (· ⊛ ·) (c, false) gps
  let scanT := scan1 PTm.op syms
  let netT := prefixNet PTm.op syms
  [ { file := "adder_row_law", name := "The row law",
      statement := "snoc ∘ row fullAdd c = adder (scanl carry c)",
      start := node xs,
      before := [("row fullAdd c", node (row fullAdd c xs)), ("snoc", node (snoc (row fullAdd c xs)))],
      after := [("scanl carry c", node (scanl carry c xs)),
        ("sumBits xs", node (adder (scanl carry c) xs))],
      note := ["c = 1", "adder net xs = sumBits xs (net xs)"] },
    { file := "adder_carry_ev", name := "carry = g ∨ (p ∧ c)",
      statement := "scanl carry c = scanl ev c ∘ map gp",
      start := node xs,
      before := [("scanl carry c", node (scanl carry c xs))],
      after := [("map gp", node gps), ("scanl ev c", node (scanl ev c gps))],
      note := ["c = 1", "carry c (a, b) = (a ∧ b) ∨ (c ∧ (a ∨ b))", "gp (a, b) = (a ∧ b, a ⊕ b)",
        "ev c (g, p) = g ∨ (p ∧ c)"] },
    { file := "adder_scan_fusion", name := "Scan fusion",
      statement := "scanl ev c = map fst ∘ scanl (⊛) (c, false)",
      start := node gps,
      before := [("scanl ev c", node (scanl ev c gps))],
      after := [("scanl (⊛) (c, false)", node pairs), ("map fst", node (map Prod.fst pairs))],
      note := ["c = 1", "(g₁, p₁) ⊛ (g₂, p₂) = (g₂ ∨ (p₂ ∧ g₁), p₁ ∧ p₂)",
        "fst (q ⊛ x) = ev (fst q) x, and fst (c, false) = c"] },
    { file := "adder_scan1", name := "Definition of scan1",
      statement := "scanl (⊛) (c, false) = scan1 (⊛) ∘ ((c, false) :: ·)",
      start := node gps,
      before := [("scanl (⊛) (c, false)", node pairs)],
      after := [("((c, false) :: ·)", node qs), ("scan1 (⊛)", node (scan1 (· ⊛ ·) qs))],
      note := ["c = 1"] },
    { file := "adder_parallel_prefix", name := "Parallel prefix",
      statement := "scan1 (⊛) = prefixNet (⊛), because ⊛ is associative",
      start := node2 (syms.map PTm.text) qs,
      before := [("scan1 (⊛)", node2 (scanT.map PTm.text) ((scanT.mapM (PTm.eval qs)).getD []))],
      after := [("prefixNet (⊛)", node2 (netT.map PTm.text) ((netT.mapM (PTm.eval qs)).getD []))],
      note := ["(a ⊛ b) ⊛ c = a ⊛ (b ⊛ c)"] } ]

/-! ## Circuits as terms

A schematic is built by running the derivation's own functions on symbolic
wires. A wire is an input column, or an output of a cell. -/

/-- The kinds of cell. -/
inductive Kind where
  /-- A full adder: output 0 is the sum bit, output 1 the carry out. -/
  | fa
  /-- `carry`: the majority of the carry in and the column's two bits. -/
  | maj
  | gp
  | ev
  /-- The carry operator `⊛`. -/
  | dot
  /-- A sum bit: the column's two bits and the carry into it. -/
  | xor
  deriving BEq, Inhabited

/-- A wire: column `k`'s input, or output `out` of a cell. Column 0 is the
carry in, and column `i + 1` holds bit `i` of each operand. -/
inductive Wire where
  | inp (k : Nat)
  | cell (kind : Kind) (args : List Wire) (out : Nat)
  deriving BEq, Inhabited

/-- The column of a wire: a cell sits in the highest column it reads. -/
partial def Wire.col : Wire → Nat
  | .inp k => k
  | .cell _ args _ => args.foldl (fun m a => max m a.col) 0

/-- The level of a wire: the cells on its longest path from the inputs. -/
partial def Wire.lvl : Wire → Nat
  | .inp _ => 0
  | .cell _ args _ => args.foldl (fun m a => max m a.lvl) 0 + 1

/-- Every cell that a wire depends on, with repeats. -/
partial def Wire.cells : Wire → List (Kind × List Wire)
  | .inp _ => []
  | .cell k args _ => (k, args) :: args.flatMap Wire.cells

/-- The columns of an adder of `n` bits. -/
def n : Nat := 7

def cin : Wire := .inp 0
def cols : List Wire := (List.range n).map fun i => .inp (i + 1)
def gpW : List Wire := cols.map fun x => .cell .gp [x] 0
def dotW (a b : Wire) : Wire := .cell .dot [a, b] 0

/-- `adder`'s outputs around carries `cs`, as `sumBits` builds them: one sum cell
per column, reading the column and the carry into it, then the last carry. -/
def adderOuts (cs : List Wire) : List Wire :=
  List.zipWith (fun x c => Wire.cell .xor [x, c] 0) cols cs ++ [cs.getLast?.getD cin]

/-- The circuit at one line of the `calc` block. -/
structure Circuit where
  file : String
  name : String
  /-- The line, as the `calc` block writes it. -/
  line : String
  /-- The carry in enters as the pair `(c, false)`. -/
  pairs : Bool := false
  /-- The sum bits, then the carry out. -/
  outs : List Wire
  deriving Inhabited

/-- The circuit of line 5, which only moves the carry in into the scan's list. -/
def line5 : List Wire := adderOuts (scan1 dotW (cin :: gpW))

/-- The circuits of `refine_cla_from_ripple_carry`: lines 1 to 4, then line 6.
Line 5 builds the same circuit as line 4, and line 7 only names line 6. -/
def circuits : List Circuit :=
  [ { file := "adder_circuit_ripple", name := "A row of full adders",
      line := "snoc ∘ row fullAdd c",
      outs := let r := row (fun c x => (Wire.cell .fa [c, x] 0, Wire.cell .fa [c, x] 1)) cin cols
        r.1 ++ [r.2] },
    { file := "adder_circuit_carry_chain", name := "A carry chain, then a sum cell per column",
      line := "adder (scanl carry c)",
      outs := adderOuts (scanl (fun c x => .cell .maj [c, x] 0) cin cols) },
    { file := "adder_circuit_gp", name := "Generate and propagate, then the chain",
      line := "adder (scanl ev c ∘ map gp)",
      outs := adderOuts (scanl (fun c q => .cell .ev [c, q] 0) cin gpW) },
    { file := "adder_circuit_scan", name := "A scan of (g, p) pairs",
      line := "adder (map fst ∘ scanl (⊛) (c, false) ∘ map gp)", pairs := true,
      outs := adderOuts (scanl dotW cin gpW) },
    { file := "adder_circuit_sklansky", name := "Sklansky's parallel prefix network",
      line := "adder (map fst ∘ prefixNet (⊛) ∘ ((c, false) :: ·) ∘ map gp)", pairs := true,
      outs := adderOuts (prefixNet dotW (cin :: gpW)) } ]

/-- The circuit drawn in file `f`. -/
def circuit (f : String) : Circuit := (circuits.find? (·.file == f)).getD default

-- Every circuit has `n` sum bits and a carry out, and every lookup below finds one.
#guard circuits.all (·.outs.length == n + 1)

-- The definition of `scan1` changes no cell: lines 4 and 5 build the same circuit.
#guard (circuit "adder_circuit_scan").outs == line5

/-! ## Checking that each circuit adds -/

/-- A value on a wire: a bit, or a pair of bits. -/
inductive V where
  | bit (b : Bool)
  | pair (q : Bool × Bool)
  deriving Inhabited

/-- A wire's bit. A carry that travels as a `(g, p)` pair is its `g`. -/
def V.toBit : V → Bool
  | .bit b => b
  | .pair q => q.1

/-- A wire's pair. `none` for a bit: no cell reads a bit as a pair. -/
def V.toPair : V → Option (Bool × Bool)
  | .pair q => some q
  | .bit _ => none

/-- The value of a wire, with each cell computed by its function in `Adder.lean`.
`none` if the wire is malformed: a cell with the wrong inputs for its kind, a
bit where a pair belongs, or a column the operands do not have. -/
partial def Wire.eval (cin : V) (xs : List Col) : Wire → Option V
  | .inp 0 => some cin
  | .inp (k + 1) => xs[k]?.map .pair
  | .cell k args o => do
    let vs ← args.mapM (Wire.eval cin xs)
    match k, vs, o with
    | .fa, [a, b], 0 => return .bit (fullAdd a.toBit (← b.toPair)).1
    | .fa, [a, b], 1 => return .bit (fullAdd a.toBit (← b.toPair)).2
    | .maj, [a, b], 0 => return .bit (carry a.toBit (← b.toPair))
    | .gp, [a], 0 => return .pair (gp (← a.toPair))
    | .ev, [a, b], 0 => return .bit (ev a.toBit (← b.toPair))
    | .dot, [a, b], 0 => return .pair ((← a.toPair) ⊛ (← b.toPair))
    | .xor, [a, b], 0 => let x ← a.toPair; return .bit ((x.1 ^^ x.2) ^^ b.toBit)
    | _, _, _ => none

/-- What is wrong with a circuit, if anything: an output it cannot evaluate, or
the first sum it gets wrong, over every pair of `n`-bit operands and both
carries in. -/
def Circuit.wrongSum (k : Circuit) : Option String :=
  (List.range (2 ^ (2 * n + 1))).findSome? fun m =>
    let (a, b, ci) := (m % 2 ^ n, m / 2 ^ n % 2 ^ n, m / 2 ^ (2 * n) == 1)
    let cv := if k.pairs then V.pair (ci, false) else .bit ci
    match k.outs.mapM fun w => w.eval cv ((bitsOf n a).zip (bitsOf n b)) with
    | none => some "an output cannot be evaluated"
    | some out =>
      if val (out.map V.toBit) == a + b + ci.toNat then none
      else some s!"the circuit gets {a} + {b} + {ci.toNat} wrong"

/-- A wrong adder, for the check below: its sum cells read the carry out of
their own column instead of the carry into it. -/
def offByOne : Circuit :=
  { file := "", name := "", line := "",
    outs := adderOuts ((scanl (fun c x => Wire.cell .maj [c, x] 0) cin cols).drop 1 ++ [cin]) }

#guard offByOne.wrongSum.isSome

-- A cell with a missing input is caught too.
#guard ({ offByOne with outs := [.cell .maj [cin] 0] } : Circuit).wrongSum ==
  some "an output cannot be evaluated"

/-! ## Drawing a circuit -/

/-- The gap between columns, and between levels. -/
def dx : Float := 64
def dy : Float := 44

/-- The x of column `k`. Columns 0 to `n` feed the carry network, and column
`n + 1` takes the carry out. -/
def colX (k : Nat) : Float := M + 36 + dx * k.toFloat

/-- The baseline of the column labels, and the top of the input wires. -/
def labelY : Float := top0 + 4
def wireTop : Float := top0 + 14

/-- The y of level `l`. Level 0 is the inputs. -/
def levelY (l : Nat) : Float := wireTop + dy * l.toFloat

/-- A cell, placed: sum cells share the row below the carry network. -/
structure Placed where
  kind : Kind
  args : List Wire
  col : Nat
  lvl : Nat

def Placed.x (p : Placed) : Float := colX p.col
def Placed.y (p : Placed) : Float := levelY p.lvl

/-- Half the width and height of a cell's symbol. -/
def Kind.half : Kind → Float × Float
  | .dot => (5, 5)
  | .xor => (9, 9)
  | _ => (16, 10)

def Kind.label : Kind → String
  | .fa => "FA"
  | .maj => "maj"
  | .gp => "gp"
  | .ev => "ev"
  | .dot => "⊛"
  | .xor => "⊕"

/-- The cells of a circuit, each once, and its carry chain: the levels holding
cells other than `gp` and sum cells. -/
def Circuit.placed (k : Circuit) : List Placed × Nat × Nat :=
  let cells := (k.outs.flatMap Wire.cells).foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  let w (kd : Kind) (args : List Wire) := Wire.cell kd args 0
  let chain := cells.filter fun (kd, _) => kd != .gp && kd != .xor
  let lo := chain.foldl (fun m (kd, a) => min m (w kd a).lvl) 1000
  let hi := chain.foldl (fun m (kd, a) => max m (w kd a).lvl) 0
  let bottom := cells.foldl (fun m (kd, a) => if kd == .xor then m else max m (w kd a).lvl) 0
  (cells.map fun (kd, a) =>
    { kind := kd, args := a, col := (w kd a).col,
      lvl := if kd == .xor then bottom + 1 else (w kd a).lvl }, lo, hi)

/-- The depth of a circuit's carry chain, in levels. -/
def Circuit.depth (k : Circuit) : Nat :=
  let (_, lo, hi) := k.placed
  hi + 1 - lo

-- The numbers the README quotes: a 7-level chain, until Sklansky's network of
-- twelve `⊛` cells takes 3 levels. On the four inputs of the law diagram, the
-- scan's last result waits 3 levels and Sklansky's 2.
#guard ["adder_circuit_ripple", "adder_circuit_carry_chain", "adder_circuit_gp",
  "adder_circuit_scan"].all fun f => (circuit f).depth == 7
#guard (circuit "adder_circuit_sklansky").depth == 3
#guard ((circuit "adder_circuit_sklansky").placed.1.filter (·.kind == .dot)).length == 12
#guard (scan1 later (List.replicate 4 0)).foldl max 0 == 3 &&
  (prefixNet later (List.replicate 4 0)).foldl max 0 == 2

/-- A wire drawn on the page, and the cells at its two ends, which it may touch. -/
structure Route where
  pts : List (Float × Float)
  dashed : Bool := false
  ends : List (Nat × Nat) := []

/-- Where a wire starts: the bottom of its column label, or its cell.
`Circuit.fault` rejects a drawing with a wire whose cell is not placed. -/
def srcAt (ps : List Placed) (w : Wire) : Nat × Nat × Float × Float :=
  match w with
  | .inp k => (k, 0, colX k, wireTop)
  | .cell kd args _ =>
    match ps.find? (fun p => p.kind == kd && p.args == args) with
    | some p => (p.col, p.lvl, p.x, p.y)
    | none => (w.col, w.lvl, colX w.col, levelY w.lvl)

/-- The wire from `w` into cell `d`. Within a column it runs straight down, or
beside the column, dashed, if cells lie in between. From a column to its right
it runs down to the level above `d`, then across into `d`. -/
def route (ps : List Placed) (w : Wire) (d : Placed) : Route :=
  let (i, l, x, y) := srcAt ps w
  if i == d.col then
    if ps.any (fun p => p.col == i && l < p.lvl && p.lvl < d.lvl) then
      { pts := [(x + 24, y), (x + 24, d.y - 16), (d.x + 7, d.y - 7)], dashed := true, ends := [(d.col, d.lvl)] }
    else { pts := [(x, y), (d.x, d.y)], ends := [(i, l), (d.col, d.lvl)] }
  else
    let ym := levelY (d.lvl - 1)
    { pts := [(x, y), (x, max y ym), (d.x, d.y)], ends := [(i, l), (d.col, d.lvl)] }

/-- The baseline of the output labels, below the last row of cells. -/
def Circuit.outY (ps : List Placed) : Float :=
  levelY (ps.foldl (fun m p => max m p.lvl) 0 + 1) + 10

/-- The wire from output `w` down to its label in column `j`. The carry out
steps right into its own column first. -/
def outRoute (ps : List Placed) (w : Wire) (j : Nat) (yOut : Float) : Route :=
  let (i, l, x, y) := srcAt ps w
  if i == j then { pts := [(x, y), (x, yOut - 14)], ends := [(i, l)] }
  else { pts := [(x, y), (colX j, min (levelY (l + 1)) (yOut - 24)), (colX j, yOut - 14)], ends := [(i, l)] }

/-- Every wire of a circuit: into each cell, and out to each label. -/
def Circuit.routes (k : Circuit) : List Route :=
  let (ps, _, _) := k.placed
  let yOut := Circuit.outY ps
  ps.flatMap (fun d => d.args.map (route ps · d)) ++
  (k.outs.zip (List.range k.outs.length)).map fun (w, i) => outRoute ps w (i + 1) yOut

/-- The legend line for each kind of cell. -/
def Kind.meaning : Kind → String
  | .fa => "a full adder: the sum bit down, the carry to the right"
  | .maj => "carry c (a, b) = (a ∧ b) ∨ (c ∧ (a ∨ b))"
  | .gp => "gp (a, b) = (a ∧ b, a ⊕ b)"
  | .ev => "ev c (g, p) = g ∨ (p ∧ c)"
  | .dot => "(g₁, p₁) ⊛ (g₂, p₂) = (g₂ ∨ (p₂ ∧ g₁), p₁ ∧ p₂); a carry is a g"
  | .xor => "sᵢ = aᵢ ⊕ bᵢ ⊕ cᵢ; the dashed wire brings xᵢ down"

/-- The kinds of cell in a circuit, in a fixed order, for its legend. -/
def Circuit.kinds (k : Circuit) : List Kind :=
  let (ps, _, _) := k.placed
  [Kind.fa, .maj, .gp, .ev, .dot, .xor].filter fun kd => ps.any (·.kind == kd)

/-- The texts of a circuit's drawing, with where they sit. -/
structure Txt where
  x : Float
  y : Float
  s : String
  anchor : String := "middle"
  ink : Ink := .value

/-- The labels: column names on top, output names below, and the depth of the
carry chain on the right. -/
def Circuit.texts (k : Circuit) : List Txt :=
  let (ps, lo, hi) := k.placed
  let yOut := Circuit.outY ps
  let tops := (Txt.mk (colX 0) labelY (if k.pairs then "(c, false)" else "c") "middle" .value) ::
    (List.range n).map fun i => Txt.mk (colX (i + 1)) labelY s!"x{sub i}" "middle" .value
  let bottoms := (List.range (n + 1)).map fun i => Txt.mk (colX (i + 1)) yOut s!"s{sub i}" "middle" .value
  let xb := colX (n + 1) + 40
  let mid := (levelY lo + levelY hi) / 2
  tops ++ bottoms ++
    [⟨xb + 10, mid - 3, "carry chain", "start", .label⟩,
     ⟨xb + 10, mid + 15, s!"{k.depth} levels", "start", .label⟩]

/-- The top of the legend, and its rows: for each line, the kind of cell drawn
beside it, if any. -/
def Circuit.legend (k : Circuit) : Float × List (Option Kind × String) :=
  let (ps, _, _) := k.placed
  (Circuit.outY ps + 28,
   (none, "xᵢ = (aᵢ, bᵢ) is column i of the operands; c is the carry in") ::
     k.kinds.map fun kd => (some kd, kd.meaning))

def legendRowH : Float := 24

/-- The page: wide enough for every text, and tall enough for the legend. -/
def Circuit.size (k : Circuit) : Float × Float :=
  let (top, rows) := k.legend
  let w := (k.texts.map fun t => (textRect t.x t.y t.s t.anchor).r) ++
    rows.map (fun (_, s) => M + 44 + textW s) ++ [M + textW k.line, M + k.name.length.toFloat * 9.5]
  (w.foldl max 0 + M, top + 16 + legendRowH * rows.length.toFloat + M)

/-- A fault in a circuit's drawing: a wire whose source is not placed, a text
off the page or over another, or a wire through a cell or a text that is not
one of its ends. -/
def Circuit.fault (k : Circuit) : Option String :=
  let (ps, _, _) := k.placed
  let placed (w : Wire) : Bool := match w with
    | .inp _ => true
    | .cell kd a _ => ps.any fun p => p.kind == kd && p.args == a
  let unplaced := !(ps.all (·.args.all placed) && k.outs.all placed)
  let (W, _) := k.size
  let ts := k.texts.map fun t => (t.s, textRect t.x t.y t.s t.anchor)
  let off := ts.find? fun (_, r) => r.l < 0 || r.r > W || r.t < top0 - 28
  let clash := (List.range ts.length).findSome? fun i => (List.range i).findSome? fun j =>
    if (ts.getD i default).2.meets (ts.getD j default).2 then
      some s!"{(ts.getD j default).1} overlaps {(ts.getD i default).1}" else none
  let pts (r : Route) : List (Float × Float) :=
    (r.pts.zip (r.pts.drop 1)).flatMap fun ((x₀, y₀), (x₁, y₁)) =>
      (List.range 41).map fun i => let t := i.toFloat / 40; (x₀ + (x₁ - x₀) * t, y₀ + (y₁ - y₀) * t)
  let hit := k.routes.findSome? fun r =>
    let inCell := ps.find? fun p =>
      !(r.ends.contains (p.col, p.lvl)) &&
        let (hw, hh) := p.kind.half
        (pts r).any fun (x, y) => (x - p.x).abs < hw + 2 && (y - p.y).abs < hh + 2
    let inText := ts.find? fun (_, rc) => (pts r).any fun (x, y) => rc.contains x y
    match inCell, inText with
    | some p, _ => some s!"a wire crosses the {p.kind.label} cell in column {p.col}, level {p.lvl}"
    | none, some (s, _) => some s!"a wire crosses {s}"
    | none, none => none
  if unplaced then some "a wire comes from a cell that is not placed" else
  match off with
  | some (s, _) => some s!"{s} is off the page"
  | none => clash.orElse fun _ => hit

/-- A cell's symbol. -/
def cellSvg (th : Theme) (kd : Kind) (x y : Float) : String :=
  match kd with
  | .dot => s!"<circle cx=\"{num x}\" cy=\"{num y}\" r=\"4.5\" fill=\"{th.ink}\"/>\n"
  | .xor =>
    s!"<circle cx=\"{num x}\" cy=\"{num y}\" r=\"9\" fill=\"{th.surface}\" stroke=\"{th.ink2}\" stroke-width=\"1.5\"/>\n" ++
    s!"<path d=\"M {num (x - 9)} {num y} H {num (x + 9)} M {num x} {num (y - 9)} V {num (y + 9)}\" stroke=\"{th.ink2}\" stroke-width=\"1.5\"/>\n"
  | _ =>
    s!"<rect x=\"{num (x - 16)}\" y=\"{num (y - 10)}\" width=\"32\" height=\"20\" rx=\"3\" fill=\"{th.surface}\" stroke=\"{th.ink2}\" stroke-width=\"1.5\"/>\n" ++
    textLine th x (y + 4.5) [(kd.label, .value)]

def routeSvg (th : Theme) (r : Route) : String :=
  let d := " ".intercalate (r.pts.map fun (x, y) => s!"{num x},{num y}")
  let dash := if r.dashed then " stroke-dasharray=\"3 3\" stroke-opacity=\"0.7\"" else ""
  s!"<polyline points=\"{d}\" fill=\"none\" stroke=\"{th.ink2}\" stroke-width=\"1.25\"{dash}/>\n"

def Circuit.svg (k : Circuit) (th : Theme) : String := Id.run do
  let (ps, lo, hi) := k.placed
  let (W, H) := k.size
  let (top, rows) := k.legend
  let desc := s!"{k.name}: the circuit of the line {k.line}, for {n} columns. " ++
    s!"Its carry chain is {k.depth} levels deep."
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{num W}\" height=\"{num H}\" viewBox=\"0 0 {num W} {num H}\" font-family=\"{sans}\" role=\"img\" aria-labelledby=\"title desc\">\n"
  out := out ++ s!"<title id=\"title\">{esc k.name}</title>\n<desc id=\"desc\">{esc desc}</desc>\n"
  out := out ++ s!"<rect width=\"100%\" height=\"100%\" fill=\"{th.surface}\"/>\n"
  out := out ++ s!"<text x=\"{num M}\" y=\"36\" font-size=\"16\" font-weight=\"600\" fill=\"{th.ink}\">{esc k.name}</text>\n"
  out := out ++ s!"<g font-family=\"{mono}\" font-size=\"13\">\n"
  out := out ++ textLine th M 60 [(k.line, .label)] "start"
  for r in k.routes do
    out := out ++ routeSvg th r
  for p in ps do
    out := out ++ cellSvg th p.kind p.x p.y
  for t in k.texts do
    out := out ++ textLine th t.x t.y [(t.s, t.ink)] t.anchor
  -- The bracket beside the carry chain.
  let xb := colX (n + 1) + 40
  out := out ++ s!"<path d=\"M {num (xb - 5)} {num (levelY lo - 8)} H {num xb} V {num (levelY hi + 8)} H {num (xb - 5)}\" fill=\"none\" stroke=\"{th.ink2}\" stroke-width=\"1.25\"/>\n"
  -- The legend.
  out := out ++ s!"<rect x=\"{num M}\" y=\"{num top}\" width=\"{num (W - 2 * M)}\" height=\"{num (16 + legendRowH * rows.length.toFloat)}\" rx=\"4\" fill=\"{th.note}\" stroke=\"{th.noteEdge}\"/>\n"
  for i in [0:rows.length] do
    let (kd, s) := rows.getD i (none, "")
    let y := top + 8 + legendRowH * (i.toFloat + 0.5)
    if let some kd := kd then
      out := out ++ cellSvg th kd (M + 24) y
    out := out ++ textLine th (M + 48) (y + 4.5) [(s, .label)] "start"
  out := out ++ "</g>\n</svg>\n"
  return out

/-- A circuit's drawing, if it adds and its layout has no fault. -/
def Circuit.drawing (k : Circuit) : Drawing := do
  if let some e := k.wrongSum then throw s!"{k.name}: {e}"
  if let some f := k.fault then throw s!"{k.name}: {f}"
  return k.svg

def main : IO UInt32 :=
  writeAll "adder_diagrams" "Adder/diagrams"
    (laws.map (fun l => (l.file, l.drawing)) ++ circuits.map (fun k => (k.file, k.drawing)))

end AdderDiagrams

def main : IO UInt32 := AdderDiagrams.main
