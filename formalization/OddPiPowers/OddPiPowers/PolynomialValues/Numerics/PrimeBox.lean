module

public import OddPiPowers.PolynomialValues.FourPeriod.ShapeUnits
public import Mathlib.Data.Int.Basic

/-! Integer checks for disjoint open trapezoids in inverse prime scale and
reduced residue. Both endpoint floor directions use exact signed division. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

structure Abscissa where
  num : ℕ
  den : ℕ
deriving DecidableEq

/-- The line value is slope times t/10000 plus offset/2. -/
structure Boundary where
  slope : ℤ
  offset : ℤ
deriving DecidableEq

structure Box where
  bottom : Boundary
  top : Boundary
  dual : ℤ
  gain : ℕ
  credit : ℕ
deriving DecidableEq

structure Slab where
  left : Abscissa
  right : Abscissa
  boxes : List Box
deriving DecidableEq

def creditScale : ℕ := 10 ^ 19

def Boundary.ordinate (l : Boundary) (t : Abscissa) : ℤ :=
  2 * l.slope * t.num + 10000 * l.offset * t.den

def Boundary.lowerFloor (l : Boundary) (t : Abscissa) : ℤ := l.ordinate t / (20000 * t.den : ℤ)

def Boundary.strictUpperFloor (l : Boundary) (t : Abscissa) : ℤ :=
  (l.ordinate t - 1) / (20000 * t.den : ℤ)

def widthMinus (w : ℕ) (l : Boundary) : Boundary := ⟨(w : ℤ) - l.slope, -l.offset⟩
def widthPlus (w : ℕ) (l : Boundary) : Boundary := ⟨(w : ℤ) + l.slope, l.offset⟩

def lowBand (l r : Abscissa) (b : Box) (w : ℕ) : ℤ :=
  let f := widthMinus w b.top
  let g := widthPlus w b.bottom
  1 + min (f.lowerFloor l) (f.lowerFloor r) + min (g.lowerFloor l) (g.lowerFloor r)

def highBand (l r : Abscissa) (b : Box) (w : ℕ) : ℤ :=
  let f := widthMinus w b.bottom
  let g := widthPlus w b.top
  1 + max (f.strictUpperFloor l) (f.strictUpperFloor r) + max (g.strictUpperFloor l) (g.strictUpperFloor r)

def rowFloor (s : Shape) (t : Abscissa) (ratio : ℕ) : ℤ :=
  ((s.rowUnits ratio : ℤ) * t.num) / ((s.massUnit : ℤ) * t.den)

def rowStrictUpperFloor (s : Shape) (t : Abscissa) (ratio : ℕ) : ℤ :=
  ((s.rowUnits ratio : ℤ) * t.num - 1) / ((s.massUnit : ℤ) * t.den)

def lowerExcess (s : Shape) (l r : Abscissa) (b : Box) : ℤ :=
  (s.widths.map (lowBand l r b)).sum - (s.rows.map (rowStrictUpperFloor s r)).sum

def upperExcess (s : Shape) (l r : Abscissa) (b : Box) : ℤ :=
  (s.widths.map (highBand l r b)).sum - (s.rows.map (rowFloor s l)).sum

def supportedExcess (s : Shape) (l r : Abscissa) (b : Box) : ℤ :=
  if 0 ≤ b.dual then lowerExcess s l r b else upperExcess s l r b

def dualPass (s : Shape) (l r : Abscissa) (b : Box) : Bool := decide
  (2 * (b.gain : ℤ) ≤ 2 * b.dual * supportedExcess s l r b -
    (s.rows.length : ℤ) * b.dual * (b.dual + 1))

def twiceAreaNum (l r : Abscissa) (b : Box) : ℤ :=
  let pr := (l.num * r.num : ℕ)
  let qr := (l.den * r.num : ℕ)
  let ps := (l.num * r.den : ℕ)
  ((qr : ℤ) - ps) * (4 * (b.top.slope - b.bottom.slope) * pr +
    10000 * (b.top.offset - b.bottom.offset) * ((qr : ℤ) + ps))

def areaDen (s : Shape) (l r : Abscissa) : ℕ :=
  4 * s.widths.sum * (l.num * r.num) ^ 2

def areaPass (s : Shape) (l r : Abscissa) (b : Box) : Bool := decide
  ((b.credit : ℤ) * areaDen s l r ≤ (creditScale : ℤ) * b.gain * twiceAreaNum l r b)

def linesPass (t : Abscissa) (previous : Boundary) (b : Box) : Bool := decide
  (previous.ordinate t ≤ b.bottom.ordinate t ∧ b.bottom.ordinate t ≤ b.top.ordinate t ∧
    b.top.ordinate t ≤ 10000 * (t.den : ℤ))

def boxesPass (s : Shape) (l r : Abscissa) (previous : Boundary) : List Box → Bool
  | [] => true
  | b :: bs => linesPass l previous b && linesPass r previous b &&
      decide (0 < b.gain ∧ 0 < b.credit) && dualPass s l r b && areaPass s l r b &&
      boxesPass s l r b.top bs

def Slab.validAfter (sl : Slab) (s : Shape) (prev : Abscissa) : Bool := decide
  (0 < sl.left.num ∧ 0 < sl.right.num ∧ 0 < sl.left.den ∧ 0 < sl.right.den ∧
    prev.num * sl.left.den ≤ sl.left.num * prev.den ∧
    sl.left.num * sl.right.den < sl.right.num * sl.left.den ∧ sl.right.num ≤ 100 * sl.right.den) &&
    boxesPass s sl.left sl.right ⟨0,0⟩ sl.boxes

def slabsPass (s : Shape) (prev : Abscissa) : List Slab → Bool
  | [] => true
  | t :: ts => t.validAfter s prev && slabsPass s t.right ts

def Slab.credit (sl : Slab) : ℕ := (sl.boxes.map Box.credit).sum

end PiPolynomialValues.PrimeWindow
