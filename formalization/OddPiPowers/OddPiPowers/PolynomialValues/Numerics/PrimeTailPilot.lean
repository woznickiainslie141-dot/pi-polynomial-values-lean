module

public import OddPiPowers.PolynomialValues.Numerics.PrimeTailData
import all Mathlib.Data.List.Sort

@[expose] public section

namespace PiPolynomialValues.FourPeriod

theorem quadratic_tail_first :
    quadraticShape.netTailIntegral 1 (1/2) quadraticShape.largestRowQ =
      1276293398837861661 / 2458823424245120000 := by
  decide +kernel

theorem cubic_tail_first :
    cubicShape.netTailIntegral 1 (1/2) cubicShape.largestRowQ =
      222761371727914077 / 816752647012360000 := by
  decide +kernel

end PiPolynomialValues.FourPeriod
