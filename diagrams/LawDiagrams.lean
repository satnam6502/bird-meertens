/-!
# Diagrams of laws, in the style of the Wikipedia article on Bird–Meertens

The drawing code shared by `kadane_diagrams`, `adder_diagrams` and
`crc_diagrams`. A `Law` is one step of a derivation, applied to an example: a
start value, and two paths from it, the line before the step and the line
after it. `Law.drawing` lays a law out and checks it. Both paths must end at the same value, as drawn, and no
text may overlap other text, leave the page or lie under a line. `writeAll`
writes the light and dark SVGs, but only if every drawing passes.
-/

namespace LawDiagrams

/-! ## Values as text -/

/-- What a run of text is. That picks its colour. -/
inductive Ink where
  /-- A number or an expression. -/
  | value
  /-- An arrow's label, or an `=`. -/
  | label
  /-- The brackets and commas of a list whose elements are lists `k` deep. -/
  | bracket (k : Nat)
  deriving BEq

/-- A run of text in one colour. -/
abbrev Span := String × Ink

/-- An integer, with a true minus sign. -/
def int (x : Int) : String := if x < 0 then s!"−{x.natAbs}" else toString x

/-- Values a diagram can show. A list's brackets are coloured by the depth of
its elements, so a list of numbers has one colour wherever it appears. -/
class Draw (α : Type) where
  /-- How deeply lists nest: `0` for a number. -/
  depth : Nat
  spans : α → List Span

instance : Draw Int := ⟨0, fun x => [(int x, .value)]⟩

/-- An expression, already written out. -/
instance : Draw String := ⟨0, fun s => [(s, .value)]⟩

instance : Draw Bool := ⟨0, fun b => [(if b then "1" else "0", .value)]⟩

instance {α β : Type} [Draw α] [Draw β] : Draw (α × β) :=
  ⟨0, fun (a, b) => [("(", .value)] ++ Draw.spans a ++ [(", ", .value)] ++ Draw.spans b ++ [(")", .value)]⟩

instance {α : Type} [Draw α] : Draw (List α) where
  depth := Draw.depth (α := α) + 1
  spans xs :=
    let c := Ink.bracket (Draw.depth (α := α))
    [("[", c)] ++ ((xs.map Draw.spans).intersperse [(", ", c)]).flatten ++ [("]", c)]

/-- A node of a diagram: lines of text, each centred. -/
abbrev Node := List (List Span)

/-- The text of a line, without its colours. -/
def lineText (l : List Span) : String := String.join (l.map (·.1))

/-- A node showing one value. -/
def node {α : Type} [Draw α] (x : α) : Node := [Draw.spans x]

/-- A node showing an expression, then its value. -/
def node2 {α β : Type} [Draw α] [Draw β] (e : α) (v : β) : Node :=
  [Draw.spans e, ("= ", .label) :: Draw.spans v]

/-! ## Laws -/

/-- One law, applied where the derivation uses it. -/
structure Law where
  /-- The name of the law's theorem. It names the files. -/
  file : String
  name : String
  /-- The law, as its derivation states it. -/
  statement : String
  /-- The value the law is applied to. -/
  start : Node
  /-- The line before the step: each arrow's label, and the value it reaches. -/
  before : List (String × Node)
  /-- The line after the step. -/
  after : List (String × Node)
  /-- Definitions of the operators, shown under the diagram. -/
  note : List String := []
  /-- Run a long path down a column, and arc the one-arrow path round it.
  This suits a path whose middle values are much wider than its ends. -/
  arc : Bool := false

/-- The value a path ends at, as drawn: the last line of its last node,
without the `= ` that puts a value under an expression. -/
def result (path : List (String × Node)) : String :=
  let l := ((path.getLast?.map (·.2)).getD []).getLastD []
  lineText (match l with
    | (s, i) :: v => if s == "= " && i == .label then v else l
    | [] => [])


/-! ## Layout -/

/-- Outer margin. -/
def M : Float := 24
/-- The advance of one character of the 13 px monospace font. -/
def cw : Float := 7.8
def lineH : Float := 20
/-- The least vertical gap between two rows of nodes. -/
def gapY : Float := 64
/-- The top of the first row, below the title. -/
def top0 : Float := 92

def textW (s : String) : Float := s.length.toFloat * cw

def nodeW (n : Node) : Float := n.foldl (fun m l => max m (textW (lineText l))) 0

def nodeH (n : Node) : Float := n.length.toFloat * lineH

def clamp (x lo hi : Float) : Float := max lo (min x hi)

/-- A node placed on the page: centred on `cx`, with its top at `y`. -/
structure Box where
  node : Node
  cx : Float
  y : Float
  deriving Inhabited

def Box.w (b : Box) : Float := nodeW b.node
def Box.h (b : Box) : Float := nodeH b.node

/-- The point of the box's top or bottom edge nearest to `x` that an arrow may
use. A short node still leaves room for two arrows to arrive apart. -/
def Box.reach (b : Box) (x : Float) : Float :=
  let r := max (b.w / 2 - 12) 10
  clamp x (b.cx - r) (b.cx + r)

/-- An arrow from the bottom of `src` to the top of `dst`. Its ends lie as
close to `x₀` and `x₁` as the boxes allow. An arrow with `x₀ = x₁` stays
vertical if its start has to move. -/
structure Arrow where
  src : Box
  dst : Box
  x₀ : Float
  x₁ : Float
  label : String
  /-- The label sits on the arrow's left. -/
  onLeft : Bool

def Arrow.ends (a : Arrow) : (Float × Float) × (Float × Float) :=
  let p₀ := a.src.reach a.x₀
  ((p₀, a.src.y + a.src.h + 2), (a.dst.reach (if a.x₁ == a.x₀ then p₀ else a.x₁), a.dst.y - 2))

/-- An arrow that leaves one node sideways at `(x₀, y₀)`, bends out to `xE`
and comes back into another at `(x₃, y₃)`: a cubic Bézier curve. -/
structure Arc where
  x₀ : Float
  y₀ : Float
  xE : Float
  x₃ : Float
  y₃ : Float
  label : String

/-- The point halfway along the arc, where it bends out furthest. -/
def Arc.apex (a : Arc) : Float := 0.125 * a.x₀ + 0.75 * a.xE + 0.125 * a.x₃

/-- The point a fraction `t` of the way along the arc. -/
def Arc.at (a : Arc) (t : Float) : Float × Float :=
  let u := 1 - t
  (u * u * u * a.x₀ + 3 * u * t * a.xE + t * t * t * a.x₃,
   a.y₀ + (a.y₃ - a.y₀) * t * t * (3 - 2 * t))

/-- A laid-out diagram, before the title and the note. -/
structure Pic where
  boxes : List Box
  arrows : List Arrow
  arcs : List Arc := []
  /-- Where an `=` joins two results that are written differently. -/
  eqs : List (Float × Float)
  w : Float
  h : Float

/-- Swap left and right. -/
def Pic.mirror (p : Pic) : Pic :=
  let f (b : Box) : Box := { b with cx := p.w - b.cx }
  { p with
    boxes := p.boxes.map f
    arrows := p.arrows.map fun a =>
      { a with src := f a.src, dst := f a.dst, x₀ := p.w - a.x₀, x₁ := p.w - a.x₁,
               onLeft := !a.onLeft }
    arcs := p.arcs.map fun a => { a with x₀ := p.w - a.x₀, xE := p.w - a.xE, x₃ := p.w - a.x₃ }
    eqs := p.eqs.map fun (x, y) => (p.w - x, y) }

/-- Rows from `top0` down. Each gap is at least `gapY`, and tall enough that
no arrow across it is flatter than about 25°. -/
def rowTops (heights : List Float) (spans : List Float) : List Float := Id.run do
  let mut y := top0
  let mut out := #[]
  for i in [0:heights.length] do
    out := out.push y
    let dx := spans.getD i 0
    y := y + heights[i]! + max gapY (0.45 * dx)
  return out.toList

/-- Two paths of two arrows each, from `s` to the shared result `t`. -/
def diamond (s : Node) (a₁ : String) (l : Node) (a₂ : String)
    (b₁ : String) (r : Node) (b₂ : String) (t : Node) (minW : Float) : Pic :=
  let wl := nodeW l
  let wr := nodeW r
  let gap := max 48 (300 - (wl + wr) / 2)
  let row := wl + gap + wr
  let W := max minW (max (2 * M + row) (2 * M + max (nodeW s) (nodeW t)))
  let x0 := (W - row) / 2
  let xl := x0 + wl / 2
  let xr := x0 + wl + gap + wr / 2
  let fit (n : Node) := clamp ((xl + xr) / 2) (M + nodeW n / 2) (W - M - nodeW n / 2)
  let xs := fit s
  let xt := fit t
  let dx := max (xs - xl) (xr - xs)
  let ys := rowTops [nodeH s, max (nodeH l) (nodeH r), nodeH t] [dx, dx]
  let S : Box := ⟨s, xs, ys[0]!⟩
  let L : Box := ⟨l, xl, ys[1]!⟩
  let R : Box := ⟨r, xr, ys[1]!⟩
  let T : Box := ⟨t, xt, ys[2]!⟩
  { boxes := [S, L, R, T]
    arrows := [⟨S, L, xs - 16, xl, a₁, true⟩, ⟨S, R, xs + 16, xr, b₁, false⟩,
               ⟨L, T, xl, xt - 16, a₂, true⟩, ⟨R, T, xr, xt + 16, b₂, false⟩]
    eqs := []
    w := W
    h := T.y + T.h }

/-- A chain of arrows on the left, and one arrow on the right, both from `s`.
They meet at one node if they compute the same text. Otherwise the two results
stand side by side, joined by `=`. -/
def chain (s : Node) (steps : List (String × Node)) (b : String) (tr : Node)
    (minW : Float) : Pic := Id.run do
  let k := steps.length
  let tl := (steps.getLast?.map (·.2)).getD []
  let shared := tl == tr
  -- The nodes in the left column, and the labels of its vertical arrows.
  let col := (steps.map (·.2)).take (if shared then k - 1 else k)
  let vlabels := ((steps.map (·.1)).drop 1).take (if shared then k - 2 else k - 1)
  let wc := col.foldl (fun m n => max m (nodeW n)) 0
  let wv := vlabels.foldl (fun m a => max m (textW a)) 0
  let xl := M + max (wc / 2) (wv + 12)
  let wEnd := if shared then nodeW tr else 0
  -- Results side by side need room for both, and the `=` between them.
  let apart := if shared then 0 else xl + nodeW tl / 2 + 48 + nodeW tr / 2
  let xr := max (max (xl + wc / 2 + 40) apart) (max (xl + 160) (M + max (nodeW s) wEnd / 2))
  let W := max minW (max (xr + max (nodeW s) (nodeW tr) / 2 + M) (xr + 12 + textW b + M))
  let S0 : Box := ⟨s, xr, 0⟩
  let L0 : Box := ⟨col.head!, xl, 0⟩
  let x₀ := S0.reach xl
  let x₁ := L0.reach x₀
  let lastSpan :=
    if shared then
      let Lk : Box := ⟨col.getLast!, xl, 0⟩
      let T0 : Box := ⟨tr, xr, 0⟩
      let e₀ := Lk.reach xr
      (T0.reach (xr - 16) - e₀).abs
    else 0
  -- One row for `s`, one per node of the column, and one more for a shared result.
  let heights := [nodeH s] ++ (if shared then col.map nodeH ++ [nodeH tr]
    else (col.dropLast.map nodeH) ++ [max (nodeH tl) (nodeH tr)])
  let spans := [(x₀ - x₁).abs] ++ List.replicate (heights.length - 3) 0 ++ [lastSpan]
  let ys := rowTops heights spans
  let S : Box := ⟨s, xr, ys[0]!⟩
  let mut boxes := #[S]
  let mut arrows := #[]
  let mut prev := S
  for i in [0:col.length] do
    let B : Box := ⟨col[i]!, xl, ys[i + 1]!⟩
    let (lab, _) := steps[i]!
    arrows := arrows.push
      (if i == 0 then ⟨prev, B, x₀, x₁, lab, true⟩ else ⟨prev, B, xl, xl, lab, true⟩)
    boxes := boxes.push B
    prev := B
  let yEnd := ys.getLast!
  let mut eqs := #[]
  if shared then
    let T : Box := ⟨tr, xr, yEnd⟩
    arrows := arrows.push ⟨prev, T, xr, xr - 16, steps[k - 1]!.1, true⟩
    arrows := arrows.push ⟨S, T, xr, xr, b, false⟩
    boxes := boxes.push T
  else
    let TR : Box := ⟨tr, xr, yEnd⟩
    arrows := arrows.push ⟨S, TR, xr, xr, b, false⟩
    boxes := boxes.push TR
    eqs := eqs.push (((prev.cx + prev.w / 2) + (TR.cx - TR.w / 2)) / 2, yEnd + 14)
  let bottom := boxes.foldl (fun m (x : Box) => max m (x.y + x.h)) 0
  return { boxes := boxes.toList, arrows := arrows.toList, eqs := eqs.toList, w := W, h := bottom }

/-- One arrow on each side, from `s` to two results side by side. They are
joined by `=` if they are written differently. -/
def fork (s : Node) (a : String) (l : Node) (b : String) (r : Node) (minW : Float) : Pic :=
  let wl := nodeW l
  let wr := nodeW r
  let gap := max 48 (240 - (wl + wr) / 2)
  let row := wl + gap + wr
  let W := max minW (max (2 * M + row) (2 * M + nodeW s))
  let x0 := (W - row) / 2
  let xl := x0 + wl / 2
  let xr := x0 + wl + gap + wr / 2
  let xs := clamp ((xl + xr) / 2) (M + nodeW s / 2) (W - M - nodeW s / 2)
  let ys := rowTops [nodeH s, max (nodeH l) (nodeH r)] [max (xs - xl) (xr - xs)]
  let S : Box := ⟨s, xs, ys[0]!⟩
  let Lb : Box := ⟨l, xl, ys[1]!⟩
  let Rb : Box := ⟨r, xr, ys[1]!⟩
  { boxes := [S, Lb, Rb]
    arrows := [⟨S, Lb, xs - 16, xl, a, true⟩, ⟨S, Rb, xs + 16, xr, b, false⟩]
    eqs := if l == r then [] else [((xl + wl / 2 + xr - wr / 2) / 2, ys[1]! + 14)]
    w := W
    h := ys[1]! + max (nodeH l) (nodeH r) }

/-- How far right the arc from `(x₀, y₀)` to `(x₃, y₃)` must bend to pass
every box by 16 px, at 101 points along it. Its `x` is linear in the bend, so
each point gives a least bend directly. `none` if an end of the arc lies level
with a box, where no bend helps. -/
def bendFor (x₀ y₀ x₃ y₃ : Float) (boxes : List Box) : Option Float :=
  (List.range 101).foldlM (init := max x₀ x₃ + 24) fun xE i =>
    let t := i.toFloat / 100
    let u := 1 - t
    let y := y₀ + (y₃ - y₀) * t * t * (3 - 2 * t)
    boxes.foldlM (init := xE) fun xE b =>
      if y < b.y - 4 || y > b.y + b.h + 4 then some xE
      else
        -- The arc's `x` here is `u³·x₀ + 3ut·xE + t³·x₃`.
        let k := 3 * u * t
        if k == 0 then none
        else some (max xE ((b.cx + b.w / 2 + 16 - u * u * u * x₀ - t * t * t * x₃) / k))

/-- A chain of arrows straight down a column, and one arrow from `s` that arcs
round the column on the right. They meet at one node if they compute the same
text. Otherwise the two results stand side by side, joined by `=`. -/
def column (s : Node) (steps : List (String × Node)) (b : String) (tr : Node)
    (minW : Float) : Option Pic := do
  let tl := (steps.getLast?.map (·.2)).getD []
  let shared := tl == tr
  let col := s :: steps.map (·.2)
  let wc := col.foldl (fun m n => max m (nodeW n)) 0
  let wv := steps.foldl (fun m (a, _) => max m (textW a)) 0
  let xc := M + max (wc / 2) (wv + 12)
  let heights := col.dropLast.map nodeH ++ [max (nodeH tl) (if shared then 0 else nodeH tr)]
  let ys := rowTops heights (List.replicate steps.length 0)
  let boxes := (col.zip ys).map fun (n, y) => Box.mk n xc y
  let arrows := ((boxes.zip (boxes.drop 1)).zip steps).map fun ((p, q), (a, _)) =>
    Arrow.mk p q xc xc a true
  let S := boxes.head!
  let last := boxes.getLast!
  let E : Box := if shared then last else ⟨tr, xc + last.w / 2 + 40 + nodeW tr / 2, last.y⟩
  let edge (b : Box) := b.cx + textW (lineText (b.node.headD [])) / 2 + 8
  let xE ← bendFor (edge S) (S.y + 10) (edge E) (E.y + 10) ((boxes.drop 1).dropLast)
  let arc : Arc := ⟨edge S, S.y + 10, xE, edge E, E.y + 10, b⟩
  return {
    boxes := if shared then boxes else boxes ++ [E]
    arrows
    arcs := [arc]
    eqs := if shared then [] else [(xc + last.w / 2 + 20, last.y + 14)]
    w := max minW (max (xc + wc / 2 + M) (max (E.cx + E.w / 2 + M) (arc.apex + 12 + textW b + M)))
    h := max last.y E.y + max last.h E.h }

/-! ## Drawing -/

/-- Colours from the validated reference palette, as in the timing plot.
Brackets take the first three categorical hues, by depth; text keeps the
text colours. -/
structure Theme where
  surface : String
  ink : String
  ink2 : String
  note : String
  noteEdge : String
  depth : Nat → String

def light : Theme where
  surface := "#fcfcfb"
  ink := "#0b0b0b"
  ink2 := "#52514e"
  note := "#f0efec"
  noteEdge := "#e1e0d9"
  depth | 0 => "#2a78d6" | 1 => "#eb6834" | _ => "#1baf7a"

def dark : Theme where
  surface := "#1a1a19"
  ink := "#ffffff"
  ink2 := "#c3c2b7"
  note := "#252524"
  noteEdge := "#383835"
  depth | 0 => "#3987e5" | 1 => "#d95926" | _ => "#199e70"

def Theme.ink' (th : Theme) : Ink → String
  | .value => th.ink
  | .label => th.ink2
  | .bracket k => th.depth k

/-- `x` to one decimal. -/
def num (x : Float) : String :=
  let m := (x.abs * 10).round.toUInt64.toNat
  (if x < 0 && m != 0 then "-" else "") ++ s!"{m / 10}.{m % 10}"

/-- Escape text for SVG. -/
def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

/-- Runs of one colour, merged. -/
def merge (l : List Span) : List Span :=
  l.foldr (init := []) fun (a, i) acc => match acc with
    | (b, j) :: rest => if i == j then (a ++ b, i) :: rest else (a, i) :: acc
    | [] => [(a, i)]

def mono := "ui-monospace, SFMono-Regular, 'SF Mono', Menlo, Consolas, 'Liberation Mono', monospace"
def sans := "system-ui, -apple-system, 'Segoe UI', sans-serif"

/-- One line of coloured text, anchored at `(x, y)`. `textLength` holds it to
the width that the layout and its checks assume, whatever font draws it. -/
def textLine (th : Theme) (x y : Float) (l : List Span) (anchor := "middle") : String :=
  let body := String.join ((merge l).map fun (s, i) => s!"<tspan fill=\"{th.ink' i}\">{esc s}</tspan>")
  s!"<text x=\"{num x}\" y=\"{num y}\" text-anchor=\"{anchor}\" textLength=\"{num (textW (lineText l))}\" lengthAdjust=\"spacing\" xml:space=\"preserve\">{body}</text>\n"

def drawBox (th : Theme) (b : Box) : String := Id.run do
  let mut out := ""
  for i in [0:b.node.length] do
    out := out ++ textLine th b.cx (b.y + 14 + lineH * i.toFloat) b.node[i]!
  return out

/-- The unit vector along an arrow. -/
def Arrow.dir (a : Arrow) : Float × Float :=
  let ((x₀, y₀), (x₁, y₁)) := a.ends
  let len := Float.sqrt ((x₁ - x₀) * (x₁ - x₀) + (y₁ - y₀) * (y₁ - y₀))
  ((x₁ - x₀) / len, (y₁ - y₀) / len)

/-- Where an arrow's label goes, beside its midpoint: the anchor, the
baseline and the `text-anchor`. -/
def Arrow.labelAt (a : Arrow) : Float × Float × String :=
  let ((x₀, y₀), (x₁, y₁)) := a.ends
  let (ux, uy) := a.dir
  -- The normal on the label's side.
  let (nx, ny) := if a.onLeft then (-uy, ux) else (uy, -ux)
  let (nx, ny) := if (a.onLeft && nx > 0) || (!a.onLeft && nx < 0) then (-nx, -ny) else (nx, ny)
  ((x₀ + x₁) / 2 + 10 * nx, (y₀ + y₁) / 2 + 10 * ny + 4 + 6 * ny, if a.onLeft then "end" else "start")

/-- Where an arc's label goes, beside its apex. -/
def Arc.labelAt (a : Arc) : Float × Float × String :=
  let onRight := a.xE > a.x₀
  (a.apex + (if onRight then 10 else -10), (a.y₀ + a.y₃) / 2 + 4, if onRight then "start" else "end")

def drawArrow (th : Theme) (a : Arrow) : String :=
  let ((x₀, y₀), (x₁, y₁)) := a.ends
  let (ux, uy) := a.dir
  let pt (x y : Float) := s!"{num x},{num y}"
  let head := s!"{pt x₁ y₁} {pt (x₁ - 10 * ux + 4.5 * uy) (y₁ - 10 * uy - 4.5 * ux)} {pt (x₁ - 10 * ux - 4.5 * uy) (y₁ - 10 * uy + 4.5 * ux)}"
  let (lx, ly, anchor) := a.labelAt
  s!"<line x1=\"{num x₀}\" y1=\"{num y₀}\" x2=\"{num (x₁ - 8 * ux)}\" y2=\"{num (y₁ - 8 * uy)}\" stroke=\"{th.ink2}\" stroke-width=\"1.5\"/>\n" ++
  s!"<polygon points=\"{head}\" fill=\"{th.ink2}\"/>\n" ++
  textLine th lx ly [(a.label, .label)] anchor

def drawArc (th : Theme) (a : Arc) : String :=
  -- The arrow points left if the arc bends out to the right.
  let u : Float := if a.xE > a.x₃ then -1 else 1
  let xEnd := a.x₃ - 8 * u
  let head := s!"{num a.x₃},{num a.y₃} {num (a.x₃ - 10 * u)},{num (a.y₃ - 4.5)} {num (a.x₃ - 10 * u)},{num (a.y₃ + 4.5)}"
  let (lx, ly, anchor) := a.labelAt
  s!"<path d=\"M {num a.x₀} {num a.y₀} C {num a.xE} {num a.y₀}, {num a.xE} {num a.y₃}, {num xEnd} {num a.y₃}\" fill=\"none\" stroke=\"{th.ink2}\" stroke-width=\"1.5\"/>\n" ++
  s!"<polygon points=\"{head}\" fill=\"{th.ink2}\"/>\n" ++
  textLine th lx ly [(a.label, .label)] anchor

/-! ## Checking the layout -/

/-- A rectangle: left, top, right, bottom. -/
structure Rect where
  l : Float
  t : Float
  r : Float
  b : Float
  deriving Inhabited

def Rect.meets (a b : Rect) : Bool := a.l < b.r && b.l < a.r && a.t < b.b && b.t < a.b

def Rect.contains (r : Rect) (x y : Float) : Bool := r.l < x && x < r.r && r.t < y && y < r.b

/-- What a line of text covers, from its anchor and baseline, with 2 px to
spare at each end. Widths are estimated as `cw` per character. A browser that
draws `−`, `∘`, `⊙` or `⊗` from a fallback font may make a line a little wider
or narrower. -/
def textRect (x y : Float) (s : String) (anchor : String) : Rect :=
  let w := textW s
  let l := if anchor == "end" then x - w else if anchor == "start" then x else x - w / 2
  ⟨l - 2, y - 11, l + w + 2, y + 3⟩

/-- Every piece of text in a diagram: the lines of its nodes, its labels and
its `=` signs. -/
def Pic.texts (p : Pic) : List (String × Rect) :=
  let line (b : Box) (i : Nat) :=
    let s := lineText (b.node.getD i [])
    (s, textRect b.cx (b.y + 14 + lineH * i.toFloat) s "middle")
  let label (s : String) : Float × Float × String → String × Rect
    | (x, y, anchor) => (s, textRect x y s anchor)
  p.boxes.flatMap (fun b => (List.range b.node.length).map (line b)) ++
  p.arrows.map (fun a => label a.label a.labelAt) ++
  p.arcs.map (fun a => label a.label a.labelAt) ++
  p.eqs.map fun (x, y) => ("=", textRect x y "=" "middle")

/-- Points at most a few pixels apart along every arrow and arc. -/
def Pic.linePoints (p : Pic) : List (Float × Float) :=
  let along (f : Float → Float × Float) := (List.range 101).map fun i => f (i.toFloat / 100)
  p.arrows.flatMap (fun a =>
    let ((x₀, y₀), (x₁, y₁)) := a.ends
    along fun t => (x₀ + (x₁ - x₀) * t, y₀ + (y₁ - y₀) * t)) ++
  p.arcs.flatMap fun a => along a.at

/-- A fault in a layout: a coordinate that is not finite, a text off the page
(left or right of it, over the title, or below the last row), two texts that
overlap, or a line through a text. It checks text against the estimate in `textRect`, and
lines at the points of `linePoints`. -/
def Pic.fault (p : Pic) : Option String :=
  let ts := p.texts
  let pts := p.linePoints
  let corners := pts ++ p.boxes.map (fun (b : Box) => (b.cx, b.y)) ++
    ts.map (fun ((_, r) : String × Rect) => (r.l, r.t))
  let finite := corners.all fun (x, y) => x.isFinite && y.isFinite
  -- The page, between the statement under the title and the last row.
  let off := ts.find? fun (_, r) => r.l < 0 || r.r > p.w || r.t < top0 - 28 || r.b > p.h
  let clash := (List.range ts.length).findSome? fun i => (List.range i).findSome? fun j =>
    if ts[i]!.2.meets ts[j]!.2 then some s!"{ts[j]!.1} overlaps {ts[i]!.1}" else none
  let crossed := ts.find? fun (_, r) => pts.any fun (x, y) => r.contains x y
  if !finite then some "a coordinate is not finite" else
  match off, clash, crossed with
  | some (s, _), _, _ => some s!"{s} is off the page"
  | none, some c, _ => some c
  | none, none, some (s, _) => some s!"a line crosses {s}"
  | none, none, none => none

/-- Move a diagram `dx` to the right, on a page `dx` wider. -/
def Pic.shiftX (p : Pic) (dx : Float) : Pic :=
  let f (b : Box) : Box := { b with cx := b.cx + dx }
  { p with
    boxes := p.boxes.map f
    arrows := p.arrows.map fun a =>
      { a with src := f a.src, dst := f a.dst, x₀ := a.x₀ + dx, x₁ := a.x₁ + dx }
    arcs := p.arcs.map fun a => { a with x₀ := a.x₀ + dx, xE := a.xE + dx, x₃ := a.x₃ + dx }
    eqs := p.eqs.map fun (x, y) => (x + dx, y)
    w := p.w + dx }

/-- Keep every text at least 8 px inside the page: move the diagram right if a
label reaches past the left edge, and widen the page if one reaches past the right.
It repairs texts only. A box or an arrow past the edge is left for `Pic.fault`
to report. -/
def Pic.fit (p : Pic) : Pic :=
  let rs := p.texts.map (·.2)
  let lo := rs.foldl (fun m r => min m r.l) p.w
  let p := if lo < 8 then p.shiftX (8 - lo) else p
  let hi := p.texts.foldl (fun m (_, r) => max m r.r) 0
  if hi + 8 > p.w then { p with w := hi + 8 } else p

/-! The checks catch what they are meant to. -/

/-- Nodes and arrows on a page 100 px wide, with rows from `top0` to 300. -/
def testPic (boxes : List Box) (arrows : List Arrow := []) : Pic :=
  { boxes, arrows, eqs := [], w := 100, h := 300 }

/-- The number `n`, centred at `x`, with its top at `y`. -/
def numAt (n : Int) (x y : Float) : Box := ⟨node n, x, y⟩

#guard (testPic [numAt 1 50 top0]).fault.isNone
#guard (testPic [numAt 1 50 top0, numAt 2 54 (top0 + 4)]).fault.isSome
#guard (testPic [numAt 12345 0 top0]).fault.isSome
#guard (testPic [numAt 1 50 0]).fault.isSome
#guard (testPic [numAt 1 50 290]).fault.isSome
#guard
  -- An arrow of length 0 has no direction.
  let (a, b) := (numAt 1 50 top0, numAt 2 50 (top0 + 24))
  (testPic [a, b] [⟨a, b, 50, 50, "f", false⟩]).fault == some "a coordinate is not finite"
#guard
  let (a, b, c) := (numAt 1 50 top0, numAt 2 50 (top0 + 100), numAt 3 50 (top0 + 50))
  ((testPic [a, b, c] [⟨a, b, 50, 50, "f", false⟩]).fault.map (·.startsWith "a line crosses")).getD false
-- `fit` repairs a label past either edge: it moves the diagram right, or widens the page.
#guard (testPic [numAt 12345 0 top0]).fit.fault.isNone
#guard (testPic [numAt 12345 100 top0]).fit.fault.isNone
#guard (testPic [numAt 12345 0 top0]).fit.texts.all (·.2.l ≥ 8)
#guard result [("f", node (2 : Int))] != result [("g", node2 "e" (6 : Int))]
#guard result [("f", node (2 : Int))] == result [("g", node2 "e" (2 : Int))]

/-- The plain text of a node, for the description. -/
def plain (n : Node) : String := " ".intercalate (n.map lineText)

/-- A path, in words. -/
def walk (steps : List (String × Node)) : String :=
  ", then ".intercalate (steps.map fun (a, n) => s!"{a} gives {plain n}")

/-- Lay out a law with one or two arrows on each side, or one arrow on one side
and two or more on the other. `none` for any other shape, or if an arc cannot
clear its column. -/
def layout (l : Law) : Option Pic :=
  let minW := 2 * M + max (l.name.length.toFloat * 9.5) (textW l.statement)
  let side s steps b t := if l.arc then column s steps b t minW else some (chain s steps b t minW)
  let pic := match l.before, l.after with
    | [(a, x)], [(b, y)] => some (fork l.start a x b y minW)
    | [(a₁, x), (a₂, t)], [(b₁, y), (b₂, _)] => some (diamond l.start a₁ x a₂ b₁ y b₂ t minW)
    | steps@(_ :: _ :: _), [(b, t)] => side l.start steps b t
    | [(b, t)], steps@(_ :: _ :: _) => (side l.start steps b t).map Pic.mirror
    | _, _ => none
  pic.map Pic.fit

def svg (th : Theme) (l : Law) (p : Pic) : String := Id.run do
  let noteW := l.note.foldl (fun m s => max m (textW ("where " ++ s))) 0
  let W := max p.w (2 * M + noteW + 24)
  let p := if W > p.w then { p with w := W } else p
  let noteTop := p.h + 32
  let H := if l.note.isEmpty then p.h + M + 8 else noteTop + 16 + lineH * l.note.length.toFloat + M
  let desc := s!"{l.name}: {l.statement}. Starting from {plain l.start}, " ++
    s!"the line before the step: {walk l.before}. The line after: {walk l.after}."
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{num W}\" height=\"{num H}\" viewBox=\"0 0 {num W} {num H}\" font-family=\"{sans}\" role=\"img\" aria-labelledby=\"title desc\">\n"
  out := out ++ s!"<title id=\"title\">{esc l.name}: {esc l.statement}</title>\n"
  out := out ++ s!"<desc id=\"desc\">{esc desc}</desc>\n"
  out := out ++ s!"<rect width=\"100%\" height=\"100%\" fill=\"{th.surface}\"/>\n"
  out := out ++ s!"<text x=\"{num M}\" y=\"36\" font-size=\"16\" font-weight=\"600\" fill=\"{th.ink}\">{esc l.name}</text>\n"
  out := out ++ s!"<g font-family=\"{mono}\" font-size=\"13\">\n"
  out := out ++ textLine th M 60 [(l.statement, .label)] "start"
  for a in p.arrows do
    out := out ++ drawArrow th a
  for a in p.arcs do
    out := out ++ drawArc th a
  for b in p.boxes do
    out := out ++ drawBox th b
  for (x, y) in p.eqs do
    out := out ++ textLine th x y [("=", .label)]
  if !l.note.isEmpty then
    out := out ++ s!"<rect x=\"{num M}\" y=\"{num noteTop}\" width=\"{num (noteW + 24)}\" height=\"{num (16 + lineH * l.note.length.toFloat)}\" rx=\"4\" fill=\"{th.note}\" stroke=\"{th.noteEdge}\"/>\n"
    for i in [0:l.note.length] do
      let lead := if i == 0 then "where " else "  and "
      out := out ++ textLine th (M + 12) (noteTop + 22 + lineH * i.toFloat) [(lead, .label), (l.note[i]!, .value)] "start"
  out := out ++ "</g>\n</svg>\n"
  return out

/-- A drawing, or why it could not be made. Given a theme, it is an SVG. -/
abbrev Drawing := Except String (Theme → String)

/-- Lay out a law, check it, and return its drawing. -/
def Law.drawing (l : Law) : Drawing := do
  let (u, v) := (result l.before, result l.after)
  if u != v then throw s!"{l.name}: the paths end at {u} and {v}"
  let some p := layout l
    | throw s!"{l.name}: no layout for paths of {l.before.length} and {l.after.length} arrows"
  if let some f := p.fault then throw s!"{l.name}: {f}"
  return fun th => svg th l p

/-- Write `<stem>_light.svg` and `<stem>_dark.svg` in `dir`, such as
`Adder/diagrams`, for each drawing, but only if every drawing could be made.
`exe` names the executable in messages. -/
def writeAll (exe : String) (dir : System.FilePath) (drawings : List (String × Drawing)) :
    IO UInt32 := do
  unless ← System.FilePath.pathExists ((dir.parent.getD ".") / "README.md") do
    IO.eprintln s!"Run {exe} from the root of the repository."
    return 1
  -- Check every drawing before writing any.
  let mut done := #[]
  for (stem, d) in drawings do
    match d with
    | .error e =>
      IO.eprintln e
      return 1
    | .ok f => done := done.push (stem, f)
  IO.FS.createDirAll dir
  for (stem, f) in done do
    IO.FS.writeFile s!"{dir}/{stem}_light.svg" (f light)
    IO.FS.writeFile s!"{dir}/{stem}_dark.svg" (f dark)
    IO.println s!"{dir}/{stem}_{"{light,dark}"}.svg"
  return 0

end LawDiagrams
