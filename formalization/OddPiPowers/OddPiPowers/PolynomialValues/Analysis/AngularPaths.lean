module

public import OddPiPowers.PolynomialValues.Numerics.AngularLedger
public import OddPiPowers.PolynomialValues.Analysis.BoundarySlope
public import OddPiPowers.PolynomialValues.Analysis.CenteredExpansion

/-! A bounded signed angular prescription gives an analytic row path with
the exact endpoint phase. Its remaining coefficient is controlled by the
actual signed sine integral of that same prescription. -/

@[expose] public section

namespace PiPolynomialValues

open Real Complex Polynomial Filter Metric Set MeasureTheory
open scoped ComplexConjugate

theorem signed_form_path {z : ℚ} (hz : 0 < (z : ℝ)) (hz1 : (z : ℝ) < 1)
    (f : ArcForm) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ[X], g.eval 0=0 ∧ (∀ x : ℝ, (g.eval (x : ℂ)).im=0) ∧
      (∫ w, |(g.eval w).im-signedFold f.field w| ∂poissonLaw z)≤ε ∧
      |((z : ℝ)⁻¹-z)*(g.eval ((z : ℝ) : ℂ)).re/2-f.actual z true|≤ε := by
  have hw : ‖((z : ℝ) : ℂ)‖<1 := by simpa [abs_of_pos hz] using hz1
  obtain ⟨g,h₀,hr,ha,hb⟩ := exists_boundary_slope hz hz1
    (signedFold_integrable hw f.field_measurable (fun θ _ => f.field_abs θ))
    (Eventually.of_forall (signedFold_odd f.field)) hε
  refine ⟨g,h₀,hr,ha,?_⟩
  simpa only [signedFold_moment,(f.integral_field z hw).2] using hb

noncomputable def correctedPhase (r t : ℝ) (v : ℤ) (g : ℂ[X]) (z : ℂ) :=
  Complex.I*correctedPolynomialPath r t ((Real.pi/2)*(v : ℝ)) g z

theorem correctedPhase_spec {r t : ℝ} (hr : 0 < r) (ht : 0≤t) (ht1 : t < 1)
    (v : ℤ) (g : ℂ[X]) (h₀ : g.eval 0=0) :
    AnalyticOnNhd ℂ (correctedPhase r t v g) (closedBall 0 1) ∧
    correctedPhase r t v g 0=0 ∧ correctedPhase r t v g (r : ℂ)=FourPeriod.phasePoint v := by
  have he := correctedPolynomialPath_endpoints (v := (Real.pi/2)*(v : ℝ)) hr ht g h₀
  refine ⟨analyticOnNhd_const.mul (correctedPolynomialPath_analytic ht ht1 g),?_,?_⟩
  · simp [correctedPhase,he.1]
  · rw [correctedPhase,he.2]
    unfold FourPeriod.phasePoint
    push_cast
    ring

theorem correctedPhase_re (r t : ℝ) (v : ℤ) (g : ℂ[X]) (h : (g.eval (r : ℂ)).im=0) (z : ℂ) :
    (correctedPhase r t v g z).re= -(g.eval z).im-
      ((Real.pi/2)*(v : ℝ)-(g.eval (r : ℂ)).re)*(correctionPath r t z).im := by
  simp only [correctedPhase,correctedPolynomialPath,Complex.mul_re,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_sub,Complex.add_im,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,h,sub_zero,zero_add,mul_zero,add_zero]
  ring

end PiPolynomialValues
