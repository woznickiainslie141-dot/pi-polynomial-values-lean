module

public import OddPiPowers.PolynomialValues.Numerics.ShapeGeometry
import Mathlib.Tactic.NormNum

/-! Right-tail mass and first-moment certificates for the equal four-period
bands. Each cut is in units of 1/(slope times massUnit). -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

structure QuantileCut where
  slope : ℕ
  numerator : ℕ
deriving DecidableEq

def quadraticCuts : List QuantileCut :=
  [⟨11, 714470000⟩, ⟨10, 1968559586⟩, ⟨6, 2055941492⟩]

def cubicCuts : List QuantileCut :=
  [⟨18, 1204690000⟩, ⟨18, 3568773656⟩, ⟨16, 5384848416⟩,
   ⟨14, 6715084808⟩, ⟨12, 7562765828⟩, ⟨7, 5661844758⟩]

def QuantileCut.massNumerator (c : QuantileCut) (s : Shape) : ℕ :=
  (s.widths.map fun w => c.slope * w * s.rows.sum - c.numerator).sum

def QuantileCut.twiceMomentNumerator (c : QuantileCut) (s : Shape) : ℕ :=
  (s.widths.map fun w => (c.slope * w * s.rows.sum) ^ 2 - c.numerator ^ 2).sum

def Shape.rightMass (s : Shape) (k : ℕ) : ℕ := s.rowUnits (s.ratios.drop (k + 1)).sum

def cutTest (s : Shape) (common : ℕ) (z : QuantileCut × ℕ) : Bool := decide
  (0 < z.1.slope ∧ z.1.numerator ≤ z.1.slope * s.massUnit ∧
   z.1.slope ^ 2 ∣ common ∧ z.1.massNumerator s = z.1.slope * s.rightMass z.2)

def conservedMoment (s : Shape) (cuts : List QuantileCut) (common : ℕ) : ℕ :=
  (cuts.map fun c => (common / c.slope ^ 2) * c.twiceMomentNumerator s).sum

def momentValue (s : Shape) (cuts : List QuantileCut) (common : ℕ) : ℚ :=
  (conservedMoment s cuts common : ℚ) / (common * s.geometry.unit * s.geometry.length)

theorem quadratic_cuts_checked : quadraticCuts.length + 1 = quadraticShape.ratios.length ∧
    quadraticCuts.zipIdx.all (cutTest quadraticShape 108900) = true ∧
    conservedMoment quadraticShape quadraticCuts 108900 = 434574974796088158282360 := by
  decide +kernel

theorem cubic_cuts_checked : cubicCuts.length + 1 = cubicShape.ratios.length ∧
    cubicCuts.zipIdx.all (cutTest cubicShape 1016064) = true ∧
    conservedMoment cubicShape cubicCuts 1016064 = 38725983082536449146804224 := by
  decide +kernel

theorem quadratic_quantile_moment : momentValue quadraticShape quadraticCuts 108900 = quadraticRateData.moment := by
  rw [momentValue, quadratic_cuts_checked.2.2, quadratic_geometry_integers]
  norm_num [quadraticRateData]

theorem cubic_quantile_moment : momentValue cubicShape cubicCuts 1016064 = cubicRateData.moment := by
  rw [momentValue, cubic_cuts_checked.2.2, cubic_geometry_integers]
  norm_num [cubicRateData]

end PiPolynomialValues.FourPeriod
