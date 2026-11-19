module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs
public import OddPiPowers.PolynomialValues.Numerics.PrimeTailSound
public import OddPiPowers.PolynomialValues.Numerics.ShapeGeometry
import all Mathlib.Data.List.Sort

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open PrimeWindow

theorem cubicTail_sum : cubicShape.selectedTailIntegral cubicTailCuts = (2119861913630159453643989431756987/194606089984806783775652160000000) := by
  decide +kernel

theorem cubicTail_cuts_inside :
    cubicTailCuts.all (fun l => decide ((1/8) ≤ l ∧ l ≤ cubicShape.largestRowQ)) = true ∧
    cubicTailCuts.length = 17 := by
  decide +kernel

theorem cubicPrime_finite_cost :
    ((cubicShape.geometry.layerMoment : ℚ) - cubicShape.geometry.rankMoment) / cubicShape.geometry.length *
      cubicShape.largestRowQ - cubicShape.selectedTailIntegral cubicTailCuts -
      (((cubicSlabs.map Slab.credit).sum : ℕ) : ℚ)/creditScale ≤ cubicRateData.primeCost := by
  rw [cubicTail_sum, cubic_geometry_integers, cubicSlabs_checked.credit_eq]
  decide +kernel

end PiPolynomialValues.FourPeriod
