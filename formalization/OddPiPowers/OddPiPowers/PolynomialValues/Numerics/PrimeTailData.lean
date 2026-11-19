module

public import OddPiPowers.PolynomialValues.FourPeriod.ShapeUnits
public import Mathlib.Data.Rat.Defs

/-! One interval for each retained level of the base denominator estimate.
The residue certificate uses reciprocal-prime coordinates below all these
intervals. Values here are rational and use the integer shape itself. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def rampIntegral (w : ℚ) (k : ℕ) (l r : ℚ) : ℚ :=
  if k = 0 then w * (r-l)
  else ((max 0 (w-k*l))^2 - (max 0 (w-k*r))^2) / (2*k)

def Shape.rowMassQ (s : Shape) (i : ℕ) : ℚ := (s.rowUnits i : ℚ) / s.massUnit
def Shape.totalWidthQ (s : Shape) : ℚ := 2 * (s.widths.sum : ℚ) / 10000
def Shape.largestRowQ (s : Shape) : ℚ := s.rowMassQ (s.rows.foldl max 0)

structure TailTerm where
  num : ℕ
  den : ℕ
  grade : ℕ

def TailTerm.width (e : TailTerm) : ℚ := (e.num : ℚ)/e.den

def Shape.columnTails (s : Shape) : List TailTerm :=
  s.widths.zipIdx.map fun e => ⟨e.1, 20000, e.2⟩

def Shape.rowTails (s : Shape) : List TailTerm :=
  (List.range 4).flatMap fun c =>
    (s.residueRows c).zipIdx.map fun e => ⟨s.rowUnits e.1, s.massUnit, e.2⟩

def TailTerm.area (e : TailTerm) (h : ℕ) (l r : ℚ) : ℚ :=
  rampIntegral e.width (h-e.grade) l r

def Shape.netTailIntegral (s : Shape) (h : ℕ) (l r : ℚ) : ℚ :=
  let col := (s.columnTails.map (fun e => e.area h l r)).sum
  let row := (s.rowTails.map (fun e => e.area h l r)).sum
  (4*col-row) / s.totalWidthQ

def quadraticTailCuts : List ℚ := [
  1/2, 2/7, 19433/70000, 9407/35000, 1817/7000, 8749/35000, 50377/210000,
  599194833/2566550000, 747761413/3226520000, 172043069/762632000]

def cubicTailCuts : List ℚ := [
  1/2, 1/4, 1/6, 2/13, 1971/13000, 9691/65000, 46733/320000,
  5284170663/36973960000, 6107700527/43223080000, 3222273519/22913440000,
  36288221/260380000, 3940661939/28641800000, 4265355799/31505980000,
  1890691457/14060520000, 2168959563/16273750000, 4081395777/30985220000, 67681031/520760000]

def Shape.selectedTailIntegral (s : Shape) (cuts : List ℚ) : ℚ :=
  (cuts.zipIdx.map fun e => s.netTailIntegral (e.2+1) e.1 s.largestRowQ).sum

end PiPolynomialValues.FourPeriod
