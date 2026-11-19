module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs
public import OddPiPowers.PolynomialValues.Numerics.PrimeTailSound
public import OddPiPowers.PolynomialValues.Numerics.ShapeGeometry
import all Mathlib.Data.List.Sort

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open PrimeWindow

theorem quadraticTail_sum : quadraticShape.selectedTailIntegral quadraticTailCuts = (91169902964897395154119/14767693486016190720000) := by
  decide +kernel

theorem quadraticTail_cuts_inside :
    quadraticTailCuts.all (fun l => decide ((1/5) ≤ l ∧ l ≤ quadraticShape.largestRowQ)) = true ∧
    quadraticTailCuts.length = 10 := by
  decide +kernel

theorem quadraticPrime_finite_cost :
    ((quadraticShape.geometry.layerMoment : ℚ) - quadraticShape.geometry.rankMoment) / quadraticShape.geometry.length *
      quadraticShape.largestRowQ - quadraticShape.selectedTailIntegral quadraticTailCuts -
      (((quadraticSlabs.map Slab.credit).sum : ℕ) : ℚ)/creditScale ≤ quadraticRateData.primeCost := by
  rw [quadraticTail_sum, quadratic_geometry_integers, quadraticSlabs_checked.credit_eq]
  decide +kernel

end PiPolynomialValues.FourPeriod
