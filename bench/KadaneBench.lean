import Kadane

/-!
# Timing the Kadane derivation

Every line of the `calc` block in `mss_eq_kadane` is a program. This executable
times each line on random lists of growing length. It writes the timings to
`bench/kadane_timings.csv`. It plots them in `bench/kadane_timings_light.svg`
and `bench/kadane_timings_dark.svg`. Run it from the root of the repository:

    lake exe kadane_bench        # a line stops once one call takes over 500 ms
    lake exe kadane_bench 50     # a quick run, stopping at 50 ms

Both axes of the plot are logarithmic. A program that costs `c·nᵏ` is then a
straight line of slope `k`, so each complexity class has its own slope.
-/

namespace KadaneBench

open BirdMeertens
open List (map foldl)

local infixl:70 " ⊙ " => odot
local infixl:70 " ⊗ " => otimes

/-! ## The programs -/

/-- One line of the derivation. -/
structure Line where
  /-- The law that produced this line. -/
  law : String
  /-- The line, as the `calc` block writes it. -/
  expr : String
  /-- The exponent of its cost in Bird's figure: `3` means O(n³). -/
  degree : Nat
  /-- The program. -/
  run : List Int → Int
  deriving Inhabited

/-- The eight lines of `mss_eq_kadane`, in order. -/
def lines : List Line := [
  ⟨"specification", "maxL ∘ map sum ∘ segs", 3,
    maxL ∘ map sum ∘ segs⟩,
  ⟨"definition of segs", "maxL ∘ map sum ∘ concat ∘ map tails ∘ inits", 3,
    maxL ∘ map sum ∘ concat ∘ map tails ∘ inits⟩,
  ⟨"map promotion", "maxL ∘ concat ∘ map (map sum) ∘ map tails ∘ inits", 3,
    maxL ∘ concat ∘ map (map sum) ∘ map tails ∘ inits⟩,
  ⟨"fold promotion", "maxL ∘ map maxL ∘ map (map sum) ∘ map tails ∘ inits", 3,
    maxL ∘ map maxL ∘ map (map sum) ∘ map tails ∘ inits⟩,
  ⟨"map distributivity", "maxL ∘ map (maxL ∘ map sum ∘ tails) ∘ inits", 3,
    maxL ∘ map (maxL ∘ map sum ∘ tails) ∘ inits⟩,
  ⟨"Horner's rule", "maxL ∘ map (foldl (⊙) 0) ∘ inits", 2,
    maxL ∘ map (foldl (· ⊙ ·) 0) ∘ inits⟩,
  ⟨"scan lemma", "maxL ∘ scanl (⊙) 0", 1,
    maxL ∘ scanl (· ⊙ ·) 0⟩,
  ⟨"fold–scan fusion", "fst ∘ foldl (⊗) (0, 0)", 1,
    Prod.fst ∘ foldl (· ⊗ ·) (0, 0)⟩
]

/-- Every timed program is the specification. The proof replays the laws of
`mss_eq_kadane`, so a typo in `lines` cannot slip through. -/
theorem lines_eq_mss : ∀ l ∈ lines, l.run = mss := by
  have h₂ : maxL ∘ concat ∘ map (map sum) ∘ map tails ∘ inits = mss := by
    rw [← map_promotion]; rfl
  have h₃ : maxL ∘ map maxL ∘ map (map sum) ∘ map tails ∘ inits = mss := by
    rw [← fold_promotion]; exact h₂
  have h₄ : maxL ∘ map (maxL ∘ map sum ∘ tails) ∘ inits = mss := by
    rw [← map_distrib, ← map_distrib]; exact h₃
  have h₅ : maxL ∘ map (foldl (· ⊙ ·) 0) ∘ inits = mss := by
    rw [← horner]; exact h₄
  have h₆ : maxL ∘ scanl (· ⊙ ·) 0 = mss := by
    rw [← scan_lemma]; exact h₅
  intro l hl
  simp only [lines, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · exact h₂
  · exact h₃
  · exact h₄
  · exact h₅
  · exact h₆
  · exact mss_eq_kadane.symm

/-! ## Timing -/

/-- `n` pseudo-random integers in `[-100, 100]`. They are made at run time, so
the compiler cannot precompute any answer. -/
def randomList (n : Nat) (seed : Nat := 2026) : List Int := Id.run do
  let mut x := seed
  let mut out : Array Int := Array.mkEmpty n
  for _ in [0:n] do
    x := (1103515245 * x + 12345) % 2147483648
    out := out.push (Int.ofNat (x / 65536 % 201) - 100)
  return out.toList

/-- List lengths from 8 to 2¹⁷, in steps of `√2`. -/
def sizes : List Nat :=
  (List.range 29).map fun k => (8 * Float.pow (Float.sqrt 2) k.toFloat).round.toUInt64.toNat

/-- One call, as an action. `noinline` keeps the work between the two clock
reads instead of letting the compiler move it. -/
@[noinline] def runOnce (f : List Int → Int) (xs : List Int) : IO Int :=
  pure (f xs)

/-- `xs` itself, since `i` never gets that big. It is `noinline`, so the
compiler cannot see that, and the input of each call depends on the loop
counter. Then no compiler can hoist `f xs` out of the loop, or share one call
between iterations. -/
@[noinline] def perturb (i : Nat) (xs : List Int) : List Int :=
  if i == 0xFFFFFFFFFFFF then [] else xs

/-- Run `f xs` `reps` times. Returns the seconds taken and the answer. -/
def batch (f : List Int → Int) (xs : List Int) (reps : Nat) : IO (Float × Int) := do
  let t₀ ← IO.monoNanosNow
  let mut r : Int := 0
  for i in [0:reps] do
    r ← runOnce f (perturb i xs)
  let t₁ ← IO.monoNanosNow
  return ((t₁ - t₀).toFloat / 1e9, r)

/-- Seconds per call. The batch doubles until it lasts 20 ms. Two more batches
of that size follow, and the fastest of the three counts. -/
def timeIt (f : List Int → Int) (xs : List Int) : IO (Float × Int) := do
  let mut reps := 1
  let mut (t, r) ← batch f xs reps
  while t < 0.02 do
    reps := reps * 2
    (t, r) ← batch f xs reps
  let mut best := t / reps.toFloat
  for _ in [0:2] do
    let (t', _) ← batch f xs reps
    best := min best (t' / reps.toFloat)
  return (best, r)

/-- One measurement. -/
structure Row where
  /-- Index into `lines`. -/
  step : Nat
  n : Nat
  seconds : Float
  deriving Inhabited

/-! ## Formatting -/

/-- `x` rounded to `d` decimals. -/
def fixed (d : Nat) (x : Float) : String :=
  let p := 10 ^ d
  let m := (Float.abs x * p.toFloat).round.toUInt64.toNat
  let frac := toString (m % p)
  let body := if d = 0 then toString (m / p)
    else s!"{m / p}." ++ "".pushn '0' (d - frac.length) ++ frac
  if x < 0 && m != 0 then "-" ++ body else body

/-- Three significant figures, for `x` in `[1, 1000)`. -/
def sig3 (x : Float) : String :=
  if x ≥ 100 then fixed 0 x else if x ≥ 10 then fixed 1 x else fixed 2 x

/-- A duration in seconds, in the unit that suits it. -/
def fmtTime (t : Float) : String :=
  if t ≥ 1 then sig3 t ++ " s"
  else if t ≥ 1e-3 then sig3 (t * 1e3) ++ " ms"
  else if t ≥ 1e-6 then sig3 (t * 1e6) ++ " µs"
  else sig3 (t * 1e9) ++ " ns"

/-- `10 ^ e` seconds, for a tick label: `1 ms`, `10 ms`, `100 ms`, `1 s`. -/
def fmtPow10 (e : Int) : String :=
  let (unit, base) : String × Int :=
    if e ≥ 0 then ("s", 0) else if e ≥ -3 then ("ms", -3)
    else if e ≥ -6 then ("µs", -6) else ("ns", -9)
  s!"{10 ^ (e - base).toNat} {unit}"

/-- A count with thousands separators. -/
partial def commas (n : Nat) : String :=
  if n < 1000 then toString n
  else
    let r := toString (n % 1000)
    commas (n / 1000) ++ "," ++ "".pushn '0' (3 - r.length) ++ r

/-- Bird's cost of a line, as text. -/
def cost : Nat → String
  | 3 => "O(n³)"
  | 2 => "O(n²)"
  | _ => "O(n)"

/-- Escape text for SVG. -/
def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

/-! ## Fitting -/

/-- The least-squares slope of `log t` against `log n`. There is none for
fewer than two points. -/
def slope (pts : Array (Nat × Float)) : Option Float :=
  if pts.size < 2 then none else
  let xs := pts.map fun p => Float.log p.1.toFloat
  let ys := pts.map fun p => Float.log p.2
  let k := pts.size.toFloat
  let mx := xs.foldl (· + ·) 0 / k
  let my := ys.foldl (· + ·) 0 / k
  let sxy := (xs.zip ys).foldl (fun s (x, y) => s + (x - mx) * (y - my)) 0
  let sxx := xs.foldl (fun s x => s + (x - mx) * (x - mx)) 0
  some (sxy / sxx)

/-- The points a slope is fitted to: calls of at least 100 µs, where fixed
overheads no longer matter. Faster calls would only flatten the slope. -/
def fitPoints (rows : Array Row) (step : Nat) : Array (Nat × Float) :=
  let pts := (rows.filter (·.step == step)).map fun r => (r.n, r.seconds)
  pts.filter (·.2 ≥ 1e-4)

/-- A slope to two decimals, or a dash when a line has too few slow calls. -/
def fmtSlope : Option Float → String
  | some k => fixed 2 k
  | none => "–"

/-! ## The plot -/

/-- Colours from the validated reference palette. Series colour encodes the
complexity class; marker shape tells the steps of one class apart. -/
structure Theme where
  surface : String
  ink : String
  ink2 : String
  muted : String
  grid : String
  axis : String
  series : Nat → String

def light : Theme where
  surface := "#fcfcfb"
  ink := "#0b0b0b"
  ink2 := "#52514e"
  muted := "#898781"
  grid := "#e1e0d9"
  axis := "#c3c2b7"
  series | 3 => "#2a78d6" | 2 => "#eb6834" | _ => "#1baf7a"

def dark : Theme where
  surface := "#1a1a19"
  ink := "#ffffff"
  ink2 := "#c3c2b7"
  muted := "#898781"
  grid := "#2c2c2a"
  axis := "#383835"
  series | 3 => "#3987e5" | 2 => "#d95926" | _ => "#199e70"

/-- The position of each step within its class picks its marker. -/
def rank (ls : Array Line) (step : Nat) : Nat :=
  ((ls.extract 0 step).filter (·.degree == ls[step]!.degree)).size

/-- A marker of `shape` centred on `(x, y)`, ringed in the surface colour. -/
def marker (shape : Nat) (x y : Float) (fill ring tip : String) : String :=
  let r : Float := 4.5
  let pt (dx dy : Float) := s!"{fixed 1 (x + dx)},{fixed 1 (y + dy)}"
  let attrs := s!"fill=\"{fill}\" stroke=\"{ring}\" stroke-width=\"4\" paint-order=\"stroke\""
  let body := match shape with
    | 0 => s!"<circle cx=\"{fixed 1 x}\" cy=\"{fixed 1 y}\" r=\"{r}\" {attrs}>"
    | 1 => s!"<rect x=\"{fixed 1 (x - 3.9)}\" y=\"{fixed 1 (y - 3.9)}\" width=\"7.8\" height=\"7.8\" {attrs}>"
    | 2 => s!"<polygon points=\"{pt 0 (-1.2 * r)} {pt (-1.05 * r) (0.6 * r)} {pt (1.05 * r) (0.6 * r)}\" {attrs}>"
    | 3 => s!"<polygon points=\"{pt 0 (-1.25 * r)} {pt (1.25 * r) 0} {pt 0 (1.25 * r)} {pt (-1.25 * r) 0}\" {attrs}>"
    | _ => s!"<polygon points=\"{pt 0 (1.2 * r)} {pt (-1.05 * r) (-0.6 * r)} {pt (1.05 * r) (-0.6 * r)}\" {attrs}>"
  let close := match shape with | 0 => "</circle>" | 1 => "</rect>" | _ => "</polygon>"
  body ++ (if tip.isEmpty then "" else s!"<title>{esc tip}</title>") ++ close

/-- Draw the timings as a log–log line chart, with a legend below it. -/
def svg (th : Theme) (ls : Array Line) (rows : Array Row) (slopes : Array (Option Float))
    (budgetMs : Nat) : String := Id.run do
  let W : Float := 960
  let M : Float := 24                       -- outer margin
  let PL : Float := 88                      -- plot left
  let PR : Float := W - 104                 -- plot right; class labels sit past it
  let PT : Float := 104                     -- plot top
  let PB : Float := PT + 400                -- plot bottom
  let LY : Float := PB + 84                 -- legend header
  let rowH : Float := 26
  let H : Float := LY + rowH * (ls.size.toFloat + 1) + 52
  let log10 (x : Float) := Float.log x / Float.log 10
  let nmax := rows.foldl (fun m r => max m r.n) 1
  let tmin := rows.foldl (fun m r => min m r.seconds) 1e9
  let tmax := rows.foldl (fun m r => max m r.seconds) 0
  let xlo := log10 8 - 0.06
  let xhi := log10 nmax.toFloat + 0.06
  let ylo := (log10 tmin).floor
  let yhi := (log10 tmax).ceil
  let sx (n : Float) := PL + (log10 n - xlo) / (xhi - xlo) * (PR - PL)
  let sy (t : Float) := PB - (log10 t - ylo) / (yhi - ylo) * (PB - PT)
  let font := "system-ui, -apple-system, 'Segoe UI', sans-serif"
  let text (x y : Float) (size : Nat) (fill : String) (s : String) (extra := "") :=
    s!"<text x=\"{fixed 1 x}\" y=\"{fixed 1 y}\" font-size=\"{size}\" fill=\"{fill}\" {extra}>{esc s}</text>\n"
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{fixed 0 W}\" height=\"{fixed 0 H}\" viewBox=\"0 0 {fixed 0 W} {fixed 0 H}\" font-family=\"{font}\" role=\"img\" aria-labelledby=\"title desc\">\n"
  out := out ++ "<title id=\"title\">Running time of each line of the Kadane derivation</title>\n"
  out := out ++ "<desc id=\"desc\">Log–log plot of time per call against list length. The five O(n³) lines rise with slope 3, Horner's rule with slope 2, and the last two lines with slope 1.</desc>\n"
  out := out ++ s!"<rect width=\"100%\" height=\"100%\" fill=\"{th.surface}\"/>\n"
  -- Title and subtitle.
  out := out ++ text M 36 18 th.ink "Running time of each line of the Kadane derivation" "font-weight=\"600\""
  out := out ++ text M 60 13 th.ink2 "Both axes are logarithmic, so the slope of a line is the exponent of its cost. Colour is the complexity class."
  out := out ++ text PL (PT - 16) 12 th.muted "Time per call"
  -- Gridlines and tick labels.
  let mut e := ylo
  while e ≤ yhi do
    let y := sy (10 ^ e)
    out := out ++ s!"<line x1=\"{fixed 1 PL}\" x2=\"{fixed 1 PR}\" y1=\"{fixed 1 y}\" y2=\"{fixed 1 y}\" stroke=\"{th.grid}\" stroke-width=\"1\" shape-rendering=\"crispEdges\"/>\n"
    out := out ++ text (PL - 10) (y + 4) 12 th.muted (fmtPow10 e.toInt64.toInt) "text-anchor=\"end\" font-variant-numeric=\"tabular-nums\""
    e := e + 1
  let mut k : Float := 1
  while k ≤ xhi do
    if k ≥ xlo then
      let x := sx (10 ^ k)
      out := out ++ s!"<line x1=\"{fixed 1 x}\" x2=\"{fixed 1 x}\" y1=\"{fixed 1 PT}\" y2=\"{fixed 1 PB}\" stroke=\"{th.grid}\" stroke-width=\"1\" shape-rendering=\"crispEdges\"/>\n"
      out := out ++ text x (PB + 22) 12 th.muted (commas (10 ^ k).round.toUInt64.toNat) "text-anchor=\"middle\" font-variant-numeric=\"tabular-nums\""
    k := k + 1
  out := out ++ s!"<line x1=\"{fixed 1 PL}\" x2=\"{fixed 1 PR}\" y1=\"{fixed 1 PB}\" y2=\"{fixed 1 PB}\" stroke=\"{th.axis}\" stroke-width=\"1\" shape-rendering=\"crispEdges\"/>\n"
  out := out ++ text ((PL + PR) / 2) (PB + 48) 12 th.muted "List length n" "text-anchor=\"middle\""
  -- One line per step, with a marker and a tooltip at every measurement.
  for i in [0:ls.size] do
    let l := ls[i]!
    let pts := rows.filter (·.step == i)
    let col := th.series l.degree
    let path := " ".intercalate (pts.map fun r => s!"{fixed 1 (sx r.n.toFloat)},{fixed 1 (sy r.seconds)}").toList
    out := out ++ s!"<polyline points=\"{path}\" fill=\"none\" stroke=\"{col}\" stroke-width=\"2\" stroke-linejoin=\"round\" stroke-linecap=\"round\"/>\n"
    for r in pts do
      let tip := s!"{i + 1}. {l.law}: n = {commas r.n}, {fmtTime r.seconds}"
      out := out ++ marker (rank ls i) (sx r.n.toFloat) (sy r.seconds) col th.surface tip ++ "\n"
  -- Direct labels: each class is named at the far end of its lines, with the
  -- steps it holds. Lines of one class can coincide, so the steps are spelled out.
  for d in [3, 2, 1] do
    let ends := rows.filter fun r => ls[r.step]!.degree == d
    let steps := (List.range ls.size).filter fun i => ls[i]!.degree == d
    if h : 0 < ends.size then
      let last := ends.foldl (fun a r => if r.n > a.n || (r.n == a.n && r.seconds > a.seconds) then r else a) ends[0]
      let x := sx last.n.toFloat + 12
      let y := sy last.seconds
      let which := match steps with
        | [i] => s!"step {i + 1}"
        | i :: rest => s!"steps {i + 1}–{rest.getLast! + 1}"
        | [] => ""
      out := out ++ text x (y + 2) 14 th.ink (cost d) "font-weight=\"600\""
      out := out ++ text x (y + 18) 12 th.ink2 which
  -- The legend: one row per step.
  let cKey := M
  let cStep := M + 44
  let cLaw := M + 64
  let cExpr := M + 214
  let cCost := W - 196
  let cSlope := W - M
  out := out ++ text cStep LY 12 th.muted "Step" "text-anchor=\"end\""
  out := out ++ text cLaw LY 12 th.muted "Law"
  out := out ++ text cExpr LY 12 th.muted "Line of the calc block"
  out := out ++ text cCost LY 12 th.muted "Bird's cost"
  out := out ++ text cSlope LY 12 th.muted "Measured slope" "text-anchor=\"end\""
  out := out ++ s!"<line x1=\"{fixed 1 M}\" x2=\"{fixed 1 (W - M)}\" y1=\"{fixed 1 (LY + 9)}\" y2=\"{fixed 1 (LY + 9)}\" stroke=\"{th.grid}\" stroke-width=\"1\" shape-rendering=\"crispEdges\"/>\n"
  for i in [0:ls.size] do
    let l := ls[i]!
    let y := LY + rowH * (i.toFloat + 1)
    let col := th.series l.degree
    out := out ++ s!"<line x1=\"{fixed 1 cKey}\" x2=\"{fixed 1 (cKey + 24)}\" y1=\"{fixed 1 (y - 4)}\" y2=\"{fixed 1 (y - 4)}\" stroke=\"{col}\" stroke-width=\"2\" stroke-linecap=\"round\"/>\n"
    out := out ++ marker (rank ls i) (cKey + 12) (y - 4) col th.surface "" ++ "\n"
    out := out ++ text cStep y 13 th.ink2 (toString (i + 1)) "text-anchor=\"end\" font-variant-numeric=\"tabular-nums\""
    out := out ++ text cLaw y 13 th.ink l.law
    out := out ++ text cExpr y 13 th.ink2 l.expr
    out := out ++ text cCost y 13 th.ink (cost l.degree)
    out := out ++ text cSlope y 13 th.ink (fmtSlope slopes[i]!) "text-anchor=\"end\" font-variant-numeric=\"tabular-nums\""
  let note := s!"Best of three batches per point, on random lists. A line stops after its first call over {budgetMs} ms. Slopes are least-squares fits over calls of 100 µs or more."
  out := out ++ text M (H - 20) 12 th.muted note
  return out ++ "</svg>\n"

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  let budgetMs := (args.head? >>= String.toNat?).getD 500
  let budget := budgetMs.toFloat / 1000
  let ls := lines.toArray
  let mut active := ls.map fun _ => true
  let mut rows : Array Row := #[]
  IO.println s!"{"n".pushn ' ' 8}step"
  for n in sizes do
    if !active.any id then break
    let xs := randomList n
    let mut answer : Option Int := none
    for i in [0:ls.size] do
      if active[i]! then
        let (t, r) ← timeIt ls[i]!.run xs
        if let some a := answer then
          if a != r then
            IO.eprintln s!"step {i + 1} gave {r}, not {a}, at n = {n}"
            return 1
        answer := some r
        rows := rows.push { step := i, n, seconds := t }
        IO.println s!"{(toString n).pushn ' ' (9 - (toString n).length)}{i + 1} {ls[i]!.law}: {fmtTime t}"
        if t > budget then active := active.set! i false
  let slopes := (List.range ls.size).toArray.map fun i => slope (fitPoints rows i)
  IO.FS.createDirAll "bench"
  let mut csv := "step,law,line,cost,n,nanoseconds\n"
  for r in rows do
    let l := ls[r.step]!
    csv := csv ++ s!"{r.step + 1},\"{l.law}\",\"{l.expr}\",{cost l.degree},{r.n},{fixed 1 (r.seconds * 1e9)}\n"
  IO.FS.writeFile "bench/kadane_timings.csv" csv
  IO.FS.writeFile "bench/kadane_timings_light.svg" (svg light ls rows slopes budgetMs)
  IO.FS.writeFile "bench/kadane_timings_dark.svg" (svg dark ls rows slopes budgetMs)
  -- A summary table, in Markdown, for the README.
  IO.println "\n| Step | Law | Bird's cost | Measured slope | n = 512 | Largest n | Time there |"
  IO.println "|---|---|---|---|---|---|---|"
  for i in [0:ls.size] do
    let l := ls[i]!
    let mine := rows.filter (·.step == i)
    let at512 := (mine.find? (·.n == 512)).map (fmtTime ·.seconds) |>.getD "-"
    let last := mine.back!
    IO.println s!"| {i + 1} | {l.law} | {cost l.degree} | {fmtSlope slopes[i]!} | {at512} | {commas last.n} | {fmtTime last.seconds} |"
  return 0

end KadaneBench

def main (args : List String) : IO UInt32 := KadaneBench.main args
