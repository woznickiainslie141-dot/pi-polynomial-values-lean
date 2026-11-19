module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact first and second primitives of the spatial logarithm on the
whole real line, with the diagonal included in interval integrals. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory Filter intervalIntegral
open scoped Topology Interval

noncomputable def frequencyLog (x : ℝ) := log 2 + log x

noncomputable def logPrimitive (x : ℝ) := x*log x+(log 2-1)*x

noncomputable def energyPrimitive (x : ℝ) := x*(x*log x)/2+(log 2/2-3/4)*x^2

theorem frequencyLog_of_ne {x : ℝ} (hx : x ≠ 0) :
    frequencyLog x = log (2*|x|) := by
  rw [frequencyLog,log_mul (by norm_num) (abs_ne_zero.mpr hx),log_abs]

theorem logPrimitive_continuous : Continuous logPrimitive :=
  continuous_mul_log.add (continuous_const.mul continuous_id)

theorem energyPrimitive_deriv (x : ℝ) : HasDerivAt energyPrimitive (logPrimitive x) x := by
  by_cases hx : x=0
  · subst x
    have ht : Tendsto (fun y : ℝ => y*log y/2+(log 2/2-3/4)*y) (𝓝[≠] 0) (𝓝 0) := by
      have h : Continuous (fun y : ℝ => y*log y/2+(log 2/2-3/4)*y) := by fun_prop
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (h.tendsto 0)
    rw [hasDerivAt_iff_tendsto_slope,show logPrimitive 0 = 0 by simp [logPrimitive] ]
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y ≠ 0 := hy
    rw [slope_def_field]
    simp only [energyPrimitive,zero_mul,mul_zero,zero_div,zero_pow,OfNat.ofNat_ne_zero,
      not_false_eq_true,add_zero,sub_zero]
    field_simp [hy']
    ring
  · have h := (((hasDerivAt_id x).mul (hasDerivAt_mul_log hx)).div_const 2).add
      (((hasDerivAt_id x).pow 2).const_mul (log 2/2-3/4))
    convert h using 1
    · funext y
      simp [energyPrimitive,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
    · simp only [logPrimitive,id_eq]
      ring

theorem intervalIntegrable_frequencyLog (a b : ℝ) :
    IntervalIntegrable frequencyLog volume a b := intervalIntegrable_const.add intervalIntegrable_log'

theorem integral_frequencyLog (a b : ℝ) :
    (∫ t in a..b, frequencyLog t) = logPrimitive b-logPrimitive a := by
  rw [show frequencyLog = (fun x : ℝ => log 2 + log x) by rfl,
    intervalIntegral.integral_add intervalIntegrable_const intervalIntegrable_log',
    intervalIntegral.integral_const,integral_log]
  simp only [smul_eq_mul,logPrimitive]
  ring

theorem integral_logPrimitive (a b : ℝ) :
    (∫ t in a..b, logPrimitive t) = energyPrimitive b-energyPrimitive a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => energyPrimitive_deriv x)
    (logPrimitive_continuous.intervalIntegrable _ _)

theorem interval_log_potential (a b x : ℝ) :
    (∫ t in a..b, frequencyLog (x-t)) = logPrimitive (x-a)-logPrimitive (x-b) := by
  rw [intervalIntegral.integral_comp_sub_left,integral_frequencyLog]

theorem interval_log_interaction (a b c d : ℝ) :
    (∫ x in a..b, (∫ t in c..d, frequencyLog (x-t))) =
      energyPrimitive (b-c)-energyPrimitive (a-c)-energyPrimitive (b-d)+energyPrimitive (a-d) := by
  simp_rw [interval_log_potential]
  have hi (y : ℝ) : IntervalIntegrable (fun x => logPrimitive (x-y)) volume a b :=
    (logPrimitive_continuous.comp (by fun_prop : Continuous fun x : ℝ => x-y)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hi c) (hi d),
    intervalIntegral.integral_comp_sub_right,intervalIntegral.integral_comp_sub_right,
    integral_logPrimitive,integral_logPrimitive]
  ring

end PiPolynomialValues
