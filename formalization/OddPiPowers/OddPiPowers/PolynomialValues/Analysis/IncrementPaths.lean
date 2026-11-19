module

public import OddPiPowers.PolynomialValues.Analysis.AngularPaths
public import OddPiPowers.PolynomialValues.Analysis.AngularSupport
public import OddPiPowers.PolynomialValues.Analysis.AllocatedBlockRate
public import OddPiPowers.PolynomialValues.Analysis.SignedTailBound

/-! Build one analytic path for each adjacent increment of the node
index. The endpoint corrections are positive. The common reflection on
the upper semicircle turns each correction into its absolute value. -/

@[expose] public section

namespace PiPolynomialValues

open Filter Set Metric Polynomial MeasureTheory Finset Real
open FourPeriod

noncomputable def radiusMoment (r : ℝ) := (r⁻¹-r)/2

theorem radiusMoment_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < radiusMoment r := by
  have h : r<r⁻¹ := hr1.trans ((one_lt_inv₀ hr).mpr hr1)
  exact div_pos (sub_pos.mpr h) (by norm_num)

theorem positive_increment_path {z : ℚ} (hz : 0 < (z : ℝ)) (hz1 : (z : ℝ)<1) (f : ArcForm)
    (hdir : f.actual z true < π/2*radiusMoment z) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ[X], g.eval 0=0 ∧ (∀ x : ℝ, (g.eval (x : ℂ)).im=0) ∧
      (∫ w, |(g.eval w).im-signedFold f.field w| ∂poissonLaw z)≤ε ∧
      |radiusMoment z*(g.eval ((z : ℝ) : ℂ)).re-f.actual z true|≤ε ∧
      0<π/2-(g.eval ((z : ℝ) : ℂ)).re := by
  let κ := (π/2*radiusMoment z-f.actual z true)/2
  have hκ : 0<κ := by dsimp [κ]; linarith
  obtain ⟨g,h₀,hg,he,hp⟩ := signed_form_path hz hz1 f (lt_min hε hκ)
  have hM : |radiusMoment z*(g.eval ((z : ℝ) : ℂ)).re-f.actual z true|≤min ε κ := by
    simpa only [radiusMoment,div_mul_eq_mul_div₀] using hp
  refine ⟨g,h₀,hg,he.trans (min_le_left _ _),hM.trans (min_le_left _ _),?_⟩
  have h := (abs_le.mp (hM.trans (min_le_right _ _))).2
  have h' : (g.eval ((z : ℝ) : ℂ)).re*radiusMoment z<π/2*radiusMoment z := by
    dsimp only [κ] at h
    rw [mul_comm (g.eval ((z : ℝ) : ℂ)).re]
    linarith only [h,hdir]
  exact sub_pos.mpr ((mul_lt_mul_iff_left₀ (radiusMoment_pos hz hz1)).mp h')

def nodeSign (k : ℕ) (v : ℤ) : ℤ := if (k : ℤ) < v then 1 else if v < -(k : ℤ) then -1 else 0

theorem nodeSign_mul (k : ℕ) (v : ℤ) (d : ℝ) : (nodeSign k v : ℝ)*d=signedIncrement k v d := by
  unfold nodeSign signedIncrement
  split_ifs <;> simp

theorem nodeSign_abs (k : ℕ) (v : ℤ) : |(nodeSign k v : ℝ)|≤1 := by unfold nodeSign; split_ifs <;> norm_num

noncomputable def incrementFamily {K : ℕ} (r t : ℝ) (g : Fin K → ℂ[X]) (v : ℤ) (z : ℂ) :=
  ∑ k, (nodeSign k.val v : ℂ)*correctedPhase r t 1 (g k) z

theorem incrementFamily_spec {K : ℕ} {r t : ℝ} (hr : 0<r) (ht : 0≤t) (ht1 : t<1)
    (g : Fin K → ℂ[X]) (h₀ : ∀ k, (g k).eval 0=0) (v : ℤ)
    (hv : (∑ k : Fin K, nodeSign k.val v)=v) :
    AnalyticOnNhd ℂ (incrementFamily r t g v) (closedBall 0 1) ∧
      incrementFamily r t g v 0=0 ∧ incrementFamily r t g v (r : ℂ)=phasePoint v := by
  have H (k : Fin K) := correctedPhase_spec hr ht ht1 1 (g k) (h₀ k)
  constructor
  · intro z hz
    apply Finset.analyticAt_fun_sum
    intro k _
    exact analyticAt_const.mul ((H k).1 z hz)
  constructor
  · simp only [incrementFamily,(H _).2.1,mul_zero,sum_const_zero]
  · simp only [incrementFamily,(H _).2.2,← sum_mul,← Int.cast_sum,hv,phasePoint]
    push_cast
    ring

noncomputable def upperSide (w : ℂ) : Bool := decide (0<w.im)

theorem unit_increment_error {r t : ℝ} (hr : 0<r) (ht : 0≤t) (ht1 : t<1) (g : ℂ[X])
    (hg : (g.eval (r : ℂ)).im=0) (f : ℝ → ℝ) (w : ℂ) (hw : ‖w‖=1) (hi : w.im≠0) :
    |faceSlope (upperSide w) (correctedPhase r t 1 g w)-f (foldedAngle w)-
        (π/2-(g.eval (r : ℂ)).re)*(|(correctionPath r t w).im|)| = |(g.eval w).im-signedFold f w| := by
  have h := correctionPath_im hw r t
  have hnum : 0≤(r⁻¹+t*r)*(1-t) := by positivity
  have hden : 0≤(1-t)^2+4*t*w.re^2 := by positivity
  rcases lt_or_gt_of_ne hi with hl|hu
  · have hc : (correctionPath r t w).im≤0 := h.le.trans (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hnum hl.le) hden)
    simp only [upperSide,decide_eq_false hl.not_gt,faceSlope,Bool.false_eq_true,if_false,
      correctedPhase_re r t 1 g hg,Int.cast_one,mul_one,abs_of_nonpos hc,signedFold,boundarySign,if_pos hl,neg_one_mul]
    rw [← abs_neg ((g.eval w).im- -f (foldedAngle w))]
    apply congrArg abs
    ring
  · have hc : 0≤(correctionPath r t w).im := h.ge.trans' (div_nonneg (mul_nonneg hnum hu.le) hden)
    simp only [upperSide,decide_eq_true hu,faceSlope,if_true,correctedPhase_re r t 1 g hg,Int.cast_one,
      mul_one,abs_of_nonneg hc,signedFold,boundarySign,if_neg hu.not_gt,if_pos hu,one_mul]
    congr 1
    ring

end PiPolynomialValues
