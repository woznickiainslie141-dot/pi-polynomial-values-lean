module

public import OddPiPowers.PolynomialValues.Analysis.PoissonQuadrant
public import OddPiPowers.PolynomialValues.Numerics.ArcRational

/-! The rational mass and sine enclosures apply directly to tests of the
actual boundary point on each half-open angular cell. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory Set Filter Complex

noncomputable def arcAngle (q : ℚ) := 2*Real.arctan (q : ℝ)

theorem arcAngle_mono : Monotone arcAngle := by
  intro a b h
  exact mul_le_mul_of_nonneg_left (Real.arctan_mono (by exact_mod_cast h)) (by norm_num)

@[simp] theorem arcAngle_zero : arcAngle 0=0 := by simp [arcAngle]
@[simp] theorem arcAngle_one : arcAngle 1=π/2 := by simp [arcAngle,Real.arctan_one]; ring

noncomputable def ArcRow.gate (e : ArcRow) (θ : ℝ) : ℝ :=
  if θ∈Ioc (arcAngle e.left) (arcAngle e.right) then 1 else 0

theorem ArcRow.gate_measurable (e : ArcRow) : Measurable e.gate :=
  measurable_const.piecewise measurableSet_Ioc measurable_const

theorem ArcRow.gate_abs_le (e : ArcRow) (θ : ℝ) : |e.gate θ|≤1 := by
  unfold gate
  split_ifs <;> norm_num

theorem integral_gate (e : ArcRow) (h₁ : 0≤e.left) (h₂ : e.left≤e.right) (h₃ : e.right≤1)
    (z : ℝ) (g : ℝ → ℝ) :
    (∫ θ in 0..π/2, foldedPoisson z θ*(e.gate θ*g θ)) =
      ∫ θ in (arcAngle e.left)..(arcAngle e.right), foldedPoisson z θ*g θ := by
  let S := Ioc (arcAngle e.left) (arcAngle e.right)
  have hS : MeasurableSet S := measurableSet_Ioc
  have hd : S⊆Ioc 0 (π/2) := Ioc_subset_Ioc
    (by simpa using arcAngle_mono h₁) (by simpa using arcAngle_mono h₃)
  have he (θ : ℝ) : foldedPoisson z θ*(e.gate θ*g θ)=S.indicator (fun t => foldedPoisson z t*g t) θ := by
    change foldedPoisson z θ*((if θ∈S then 1 else 0)*g θ)=_
    by_cases h : θ∈S <;> simp [h]
  simp_rw [he]
  rw [intervalIntegral.integral_of_le (by positivity),intervalIntegral.integral_of_le (arcAngle_mono h₂),
    integral_indicator hS,Measure.restrict_restrict_of_subset hd]

theorem ArcRow.boundary_enclosed (e : ArcRow) (z : ℚ) (h : e.passes z=true) :
    (∫ w, e.gate (foldedAngle w) ∂poissonLaw z)∈Icc (e.massLo : ℝ) (e.massHi : ℝ) ∧
    (∫ w : ℂ, e.gate (foldedAngle w)*|w.im| ∂poissonLaw z)∈Icc (e.sineLo : ℝ) (e.sineHi : ℝ) := by
  obtain ⟨hz,hz',ha,hb,hc,_⟩ := of_decide_eq_true h
  have hpos : 0<(z : ℝ) := by exact_mod_cast hz
  have hlt : (z : ℝ)<1 := by exact_mod_cast hz'
  have hm := poissonLaw_fold hpos hlt e.gate_measurable (fun θ _ => e.gate_abs_le θ)
  have hs := poissonLaw_fold (f := fun θ => e.gate θ*Real.sin θ) hpos hlt (e.gate_measurable.mul Real.continuous_sin.measurable)
    (M := 1) (fun θ _ => by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (e.gate_abs_le θ) (Real.abs_sin_le_one θ) (abs_nonneg _) zero_le_one)
  have h₁ := integral_gate e ha hb hc (z : ℝ) (fun _ => 1)
  simp only [mul_one] at h₁
  have h₂ := integral_gate e ha hb hc (z : ℝ) Real.sin
  have hae : (∫ w : ℂ, e.gate (foldedAngle w)*|w.im| ∂poissonLaw z)=
      ∫ w : ℂ, e.gate (foldedAngle w)*Real.sin (foldedAngle w) ∂poissonLaw z := by
    apply integral_congr_ae
    filter_upwards [poissonLaw_unit (z : ℝ)] with w hw
    rw [foldedAngle,Real.sin_arcsin (by linarith [abs_nonneg w.im])
      ((Complex.abs_im_le_norm w).trans (le_of_eq hw))]
  rw [hm,h₁,hae,hs,h₂]
  exact e.enclosed_of_passes z h

theorem arcChain_interval {l u : ℚ} {es : List ArcRow} (h : arcChain l u es=true) : l≤u := by
  induction es generalizing l with
  | nil => exact le_of_eq (of_decide_eq_true h)
  | cons e es ih =>
    simp only [arcChain,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1.1.le.trans (h.1.2.le.trans (ih h.2))

theorem arcChain_gates {l u : ℚ} {es : List ArcRow} (h : arcChain l u es=true) (θ : ℝ) :
    (es.map fun e => e.gate θ).sum=(if θ∈Ioc (arcAngle l) (arcAngle u) then 1 else 0) := by
  induction es generalizing l with
  | nil =>
    have he : l=u := of_decide_eq_true h
    simp [he]
  | cons e es ih =>
    simp only [arcChain,Bool.and_eq_true,decide_eq_true_eq] at h
    change e.gate θ+(es.map fun t => t.gate θ).sum=_
    rw [ih h.2,h.1.1]
    simp only [ArcRow.gate,Set.mem_Ioc]
    have h₁ := arcAngle_mono h.1.2.le
    have h₂ := arcAngle_mono (arcChain_interval h.2)
    split_ifs <;> grind only

end PiPolynomialValues
