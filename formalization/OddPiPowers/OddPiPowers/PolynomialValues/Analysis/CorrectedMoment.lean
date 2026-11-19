module

public import OddPiPowers.PolynomialValues.Analysis.CorrectionPath
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Polynomial.Div

/-! The correcting path meets both endpoint conditions exactly and
its mean absolute imaginary part tends to the prescribed sine moment. -/

@[expose] public section

namespace PiPolynomialValues

open Complex Real Metric Filter Polynomial
open scoped Topology

theorem polynomial_sine_moment (p : ℂ[X]) (hp : p.eval 0=0) {r : ℝ} (hr : 0<r) (hr1 : r<1) :
    poissonMean (r : ℂ) (fun z => (p.eval z).im*z.im) =
      (r⁻¹-r)*(p.eval (r : ℂ)).re/2 := by
  obtain ⟨g,hg⟩ := X_dvd_iff.mpr ((Polynomial.coeff_zero_eq_eval_zero p).trans hp)
  subst p
  simp only [eval_mul,eval_X]
  exact path_sine_moment hr hr1 ((AnalyticOnNhd.eval_polynomial g).mono (Set.subset_univ _))

theorem correction_absolute_cost {r t : ℝ} (hr : 0<r) (hr1 : r<1) (ht : 0<t) (ht1 : t<1) :
    (r⁻¹-r)/2 ≤ poissonMean (r : ℂ) (fun z => |(correctionPath r t z).im|) ∧
      poissonMean (r : ℂ) (fun z => |(correctionPath r t z).im|) ≤
        (r⁻¹-r)/2+(r⁻¹+t*r)*(1-t)/(4*t) := by
  let F (z : ℂ) := (correctionPath r t z).im
  let E := (r⁻¹+t*r)*(1-t)/(4*t)
  have hw : ‖(r : ℂ)‖<1 := by simpa [abs_of_pos hr] using hr1
  have ha := correctionFactor_analytic ht.le ht1 r
  have hc : ContinuousOn F (sphere 0 1) :=
    Complex.continuous_im.comp_continuousOn (continuousOn_id.mul (ha.continuousOn.mono sphere_subset_closedBall))
  have hm := path_sine_moment hr hr1 ha
  change poissonMean (r : ℂ) (fun z => F z*z.im) = (r⁻¹-r)*(correctionPath r t (r : ℂ)).re/2 at hm
  rw [correctionPath_radius hr ht.le,Complex.one_re,mul_one] at hm
  have hS : ContinuousOn (fun z : ℂ => F z*z.im) (sphere 0 1) := hc.mul Complex.continuous_im.continuousOn
  constructor
  · rw [← hm]
    apply poissonMean_mono hw hS hc.abs
    intro z hz
    have hh : ‖z‖=1 := by simpa [mem_sphere,dist_eq_norm] using hz
    have hi := (Complex.abs_im_le_norm z).trans_eq hh
    calc
      _ ≤ |F z*z.im| := le_abs_self _
      _ ≤ |F z| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hi
  · change poissonMean (r : ℂ) (fun z => |F z|) ≤ (r⁻¹-r)/2+E
    rw [← hm,← poissonMean_const hw E,← poissonMean_add hw hS continuousOn_const]
    apply poissonMean_mono hw hc.abs (hS.add continuousOn_const)
    intro z hz
    have H := correctionPath_absolute_error hr ht ht1 (z := z) (by simpa [mem_sphere,dist_eq_norm] using hz)
    change |F z|≤F z*z.im+E
    dsimp only [F,E]
    linarith

theorem correction_mean_limit {ι : Type*} {G : Filter ι} {t : ι → ℝ}
    (ht : ∀ i, 0<t i) (ht1 : ∀ i, t i<1) (hlim : Tendsto t G (𝓝 1))
    {r : ℝ} (hr : 0<r) (hr1 : r<1) :
    Tendsto (fun i => poissonMean (r : ℂ) (fun z => |(correctionPath r (t i) z).im|)) G (𝓝 ((r⁻¹-r)/2)) := by
  have HE : Tendsto (fun i => (r⁻¹+t i*r)*(1-t i)/(4*t i)) G (𝓝 0) := by
    have H := (((hlim.mul_const r).const_add r⁻¹).mul (hlim.const_sub 1)).div (hlim.const_mul 4) (by norm_num)
    simpa [Pi.div_def] using H
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using HE.const_add ((r⁻¹-r)/2))
  · exact fun i => (correction_absolute_cost hr hr1 (ht i) (ht1 i)).1
  · exact fun i => (correction_absolute_cost hr hr1 (ht i) (ht1 i)).2

noncomputable def correctedPolynomialPath (r t v : ℝ) (g : ℂ[X]) (z : ℂ) :=
  g.eval z+((v : ℂ)-g.eval (r : ℂ))*correctionPath r t z

theorem correctedPolynomialPath_endpoints {r t v : ℝ} (hr : 0<r) (ht : 0≤t) (g : ℂ[X]) (hg : g.eval 0=0) :
    correctedPolynomialPath r t v g 0=0 ∧ correctedPolynomialPath r t v g (r : ℂ)=(v : ℂ) := by
  simp [correctedPolynomialPath,hg,correctionPath_radius hr ht]

theorem correctedPolynomialPath_analytic {r t v : ℝ} (ht : 0≤t) (ht1 : t<1) (g : ℂ[X]) :
    AnalyticOnNhd ℂ (correctedPolynomialPath r t v g) (closedBall 0 1) := by
  intro z hz
  exact (AnalyticOnNhd.eval_polynomial g z (Set.mem_univ z)).add
    (analyticAt_const.mul (analyticAt_id.mul (correctionFactor_analytic ht ht1 r z hz)))

end PiPolynomialValues
