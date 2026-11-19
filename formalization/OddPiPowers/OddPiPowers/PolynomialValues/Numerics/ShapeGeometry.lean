module

public import OddPiPowers.PolynomialValues.FourPeriod.ShapeUnits
public import OddPiPowers.PolynomialValues.Numerics.RateData
import all Mathlib.Data.List.Sort
import Mathlib.Tactic.NormNum

/-! Evaluate the finite degree and row-square formulas on the integer
bandwidths and the sorted four residue classes. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def Shape.shiftUnits (s : Shape) (z : ℕ) : ℕ :=
  2 * s.rows.sum * (s.widths.map (min z)).sum +
    (s.rows.map (fun a => ((List.range 2).map fun k =>
      s.rowUnits a - 2 * z * s.rows.sum - 2 * k * s.massUnit).sum)).sum

structure GeometryIntegers where
  unit : ℕ
  length : ℕ
  layerMoment : ℕ
  rankMoment : ℕ
  squareMoment : ℕ
  largestShift : ℕ
deriving DecidableEq

def Shape.geometry (s : Shape) : GeometryIntegers where
  unit := s.massUnit
  length := s.rowUnits s.rows.sum
  layerMoment := 2 * s.rows.sum * (s.widths.zipIdx.map (fun x => x.1 * x.2)).sum
  rankMoment := ((List.range 4).map fun r =>
    ((s.residueRows r).zipIdx.map fun x => s.rowUnits x.1 * x.2).sum).sum
  squareMoment := (s.rows.map (fun r => (s.rowUnits r) ^ 2)).sum
  largestShift := ((0 :: s.widths).map s.shiftUnits).foldl max 0

def GeometryIntegers.lengthValue (g : GeometryIntegers) : ℚ := (g.length : ℚ) / g.unit

def GeometryIntegers.degreeValue (g : GeometryIntegers) : ℚ :=
  ((g.length : ℚ) + g.layerMoment - g.rankMoment - g.largestShift) / g.length

def GeometryIntegers.rowSquareValue (g : GeometryIntegers) : ℚ :=
  (g.squareMoment : ℚ) / (2 * g.unit * g.length)

private def tailCheck (s : Shape) : Bool :=
  s.rows.all fun r => decide (s.rowUnits r ≤ 4 * s.massUnit)

private theorem tail_zero {s : Shape} (ht : tailCheck s = true) (r : ℕ) (hr : r ∈ s.rows)
    (z k : ℕ) (hk : 2 ≤ k) :
    s.rowUnits r - 2 * z * s.rows.sum - 2 * k * s.massUnit = 0 := by
  have hbase : s.rowUnits r ≤ 4 * s.massUnit := of_decide_eq_true (List.all_eq_true.mp ht r hr)
  have hk' : 4 * s.massUnit ≤ 2 * k * s.massUnit := by
    apply Nat.mul_le_mul_right
    omega
  exact Nat.sub_eq_zero_of_le ((Nat.sub_le _ _).trans (hbase.trans hk'))

theorem quadratic_shift_tail (r : ℕ) (hr : r ∈ quadraticShape.rows) (z k : ℕ) (hk : 2 ≤ k) :
    quadraticShape.rowUnits r - 2 * z * quadraticShape.rows.sum - 2 * k * quadraticShape.massUnit = 0 :=
  tail_zero (s := quadraticShape) (by decide +kernel) _ hr _ _ hk

theorem cubic_shift_tail (r : ℕ) (hr : r ∈ cubicShape.rows) (z k : ℕ) (hk : 2 ≤ k) :
    cubicShape.rowUnits r - 2 * z * cubicShape.rows.sum - 2 * k * cubicShape.massUnit = 0 :=
  tail_zero (s := cubicShape) (by decide +kernel) _ hr _ _ hk

theorem quadratic_geometry_integers : quadraticShape.geometry =
    ⟨586640000, 8382733616, 31956979344, 3022922570, 10319925715448805552, 10173158896⟩ := by
  decide +kernel

theorem cubic_geometry_integers : cubicShape.geometry =
    ⟨1041520000, 25094174576, 169123267424, 23470975270, 51875217013002501296, 29560079804⟩ := by
  decide +kernel

theorem quadratic_geometry_rates :
    quadraticShape.geometry.lengthValue = quadraticRateData.length ∧
    quadraticShape.geometry.degreeValue = quadraticRateData.auxDegree ∧
    quadraticShape.geometry.rowSquareValue = quadraticRateData.rowSquare := by
  rw [quadratic_geometry_integers]
  norm_num [GeometryIntegers.lengthValue, GeometryIntegers.degreeValue, GeometryIntegers.rowSquareValue,
    quadraticRateData]

theorem cubic_geometry_rates :
    cubicShape.geometry.lengthValue = cubicRateData.length ∧
    cubicShape.geometry.degreeValue = cubicRateData.auxDegree ∧
    cubicShape.geometry.rowSquareValue = cubicRateData.rowSquare := by
  rw [cubic_geometry_integers]
  norm_num [GeometryIntegers.lengthValue, GeometryIntegers.degreeValue, GeometryIntegers.rowSquareValue,
    cubicRateData]

end PiPolynomialValues.FourPeriod
