module

public import OddPiPowers.PolynomialValues.Numerics.PoissonArc
import Mathlib.Tactic.NormNum

/-! The first actual cell of the degree-two allocation, in units of 10⁻²⁰. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory

private theorem quadratic_first_arc_checks :
    arcChecks (41059/250000) 0 (9/2048)
      (590545199034372824/10^20) (590545199034372825/10^20)
      (2595132113133042/10^20) (2595132113133043/10^20) := by
  norm_num [arcChecks, arcPiLo, arcPiHi, arcMassArg, arcSineArg, halfAngleSin, halfAngleCos,
    arcOdd, Finset.sum_range_succ]

theorem quadratic_first_arc_integrals :
    (∫ t in 0..(2*arctan (9/2048)), foldedPoisson (41059/250000) t) ∈
        Set.Icc (590545199034372824/10^20) (590545199034372825/10^20) ∧
    (∫ t in 0..(2*arctan (9/2048)), foldedPoisson (41059/250000) t * sin t) ∈
        Set.Icc (2595132113133042/10^20) (2595132113133043/10^20) := by
  simpa only [arctan_zero, mul_zero] using
    (arcChecks_sound (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inr (by norm_num)) quadratic_first_arc_checks)

end PiPolynomialValues
