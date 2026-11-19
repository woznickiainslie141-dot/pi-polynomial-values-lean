module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The Poisson formula on the unit disk follows by splitting the real
kernel into the Cauchy kernel and an analytic term with value zero at
the origin. All averages use the normalized angular measure. -/

@[expose] public section

namespace PiPolynomialValues

open Complex Real Metric Set
open scoped ComplexConjugate

noncomputable def unitPoisson (w z : ℂ) : ℝ := (1-‖w‖^2)/‖z-w‖^2

theorem unitPoisson_nonneg {w : ℂ} (hw : ‖w‖ ≤ 1) (z : ℂ) : 0 ≤ unitPoisson w z := by
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg w]

theorem unitPole_ne {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) : 1-conj w*z ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  simp only [norm_one,norm_mul,Complex.norm_conj] at he
  have hle := mul_le_mul_of_nonneg_left hz (norm_nonneg w)
  linarith

theorem unitPoisson_split {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ = 1) :
    (unitPoisson w z : ℂ) = z/(z-w)+conj w*z/(1-conj w*z) := by
  have hzw : z ≠ w := by intro h; rw [h] at hz; linarith
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hz' : z*conj z=1 := by rw [Complex.mul_conj,← Complex.sq_norm,hz]; norm_num
  have ha : 1-conj w*z = z*conj (z-w) := by rw [map_sub,mul_sub,hz']; ring
  have hd : ((‖z-w‖^2 : ℝ) : ℂ) = (z-w)*conj (z-w) := by rw [Complex.mul_conj,← Complex.sq_norm]
  have he : ((‖w‖^2 : ℝ) : ℂ) = w*conj w := by rw [Complex.mul_conj,← Complex.sq_norm]
  rw [unitPoisson,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_one,he,hd,ha]
  have hn : conj (z-w) ≠ 0 := by
    intro h
    exact (sub_ne_zero.mpr hzw) ((starRingEnd ℂ).injective (h.trans (map_zero _).symm))
  field_simp [hz0,hn,sub_ne_zero.mpr hzw]
  rw [map_sub]
  linear_combination -hz'

theorem unitPoisson_continuousOn {w : ℂ} (hw : ‖w‖ < 1) :
    ContinuousOn (unitPoisson w) (sphere (0 : ℂ) 1) := by
  apply continuousOn_const.div (by fun_prop)
  intro z hz
  have h : ‖z‖=1 := by simpa [mem_sphere,dist_eq_norm] using hz
  have he : z ≠ w := by intro he; rw [he] at h; linarith
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr he))

theorem unitPoisson_mean {w : ℂ} (hw : ‖w‖ < 1) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) :
    circleAverage (fun z => (unitPoisson w z : ℂ)*f z) 0 1 = f w := by
  let A (z : ℂ) := z/(z-w)*f z
  let B (z : ℂ) := conj w*z/(1-conj w*z)*f z
  have hA : ContinuousOn A (sphere (0 : ℂ) 1) := by
    apply ContinuousOn.mul _ (hf.continuousOn.mono sphere_subset_closedBall)
    apply continuousOn_id.div (by fun_prop)
    intro z hz
    have h : ‖z‖=1 := by simpa [mem_sphere,dist_eq_norm] using hz
    exact sub_ne_zero.mpr (fun he => by rw [he] at h; linarith)
  have hB : AnalyticOnNhd ℂ B (closedBall 0 1) := by
    intro z hz
    have hu := unitPole_ne hw (by simpa [mem_closedBall,dist_eq_norm] using hz)
    exact (((analyticAt_const.mul analyticAt_id).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) hu).mul (hf z hz))
  have hD {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1)) :
      DiffContOnCl ℂ g (ball 0 |(1 : ℝ)|) := by
    apply DifferentiableOn.diffContOnCl
    simpa [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)] using hg.differentiableOn
  have he : circleAverage (fun z => (unitPoisson w z : ℂ)*f z) 0 1 =
      circleAverage (A+B) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    have h : ‖z‖=1 := by simpa [mem_sphere,dist_eq_norm] using hz
    simp only [Pi.add_apply,A,B,unitPoisson_split hw h,add_mul]
  rw [he,circleAverage_add (hA.circleIntegrable zero_le_one)
    ((hB.continuousOn.mono sphere_subset_closedBall).circleIntegrable zero_le_one)]
  have H := (hD hf).circleAverage_smul_div (w := w) (by simpa [mem_ball,dist_eq_norm] using hw)
  have H' := (hD hB).circleAverage
  change circleAverage A 0 1 + circleAverage B 0 1 = _
  rw [show circleAverage A 0 1=f w from (by simpa [A,smul_eq_mul] using H),H']
  simp [B]

end PiPolynomialValues
