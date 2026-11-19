module

public import OddPiPowers.PolynomialValues.Analysis.IntegrableMinor
public import OddPiPowers.PolynomialValues.Analysis.MinorRates
public import OddPiPowers.PolynomialValues.Analysis.PathUniformity

/-! Linear operations preserve the evaluated Poisson mean. Sampling the
actual selected minor at its interpolation phase separates the finite
origin-order gain from the integrated cost. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Filter Finset Polynomial Real MeasureTheory Metric

def HasPoissonMean (r : ℝ) (f : ℂ → ℝ) (A : ℝ) : Prop :=
  Integrable f (poissonLaw r) ∧ (∫ z, f z ∂poissonLaw r)=A

namespace HasPoissonMean

variable {r a b : ℝ} {f g : ℂ → ℝ}

theorem constant (hr : ‖(r : ℂ)‖<1) (c : ℝ) : HasPoissonMean r (fun _ => c) c := by
  letI := poissonLaw_probability hr
  exact ⟨integrable_const _,by simp⟩

theorem add (hf : HasPoissonMean r f a) (hg : HasPoissonMean r g b) :
    HasPoissonMean r (fun w => f w+g w) (a+b) :=
  ⟨hf.1.add hg.1,by rw [integral_add hf.1 hg.1,hf.2,hg.2]⟩

theorem sub (hf : HasPoissonMean r f a) (hg : HasPoissonMean r g b) :
    HasPoissonMean r (fun w => f w-g w) (a-b) :=
  ⟨hf.1.sub hg.1,by rw [integral_sub hf.1 hg.1,hf.2,hg.2]⟩

theorem left_mul (hf : HasPoissonMean r f a) (c : ℝ) : HasPoissonMean r (fun w => c*f w) (c*a) :=
  ⟨hf.1.const_mul c,by rw [integral_const_mul,hf.2]⟩

theorem right_mul (hf : HasPoissonMean r f a) (c : ℝ) : HasPoissonMean r (fun w => f w*c) (a*c) := by
  simpa only [mul_comm c] using hf.left_mul c

end HasPoissonMean

namespace SelectedSequence

variable {P : EvaluationPlan} (W : SelectedSequence P)

theorem interior_mean (i : ℕ) (h : LabelChoice (W.layer i)) {r : ℝ} (hr : 0<r) (hr1 : r<1)
    (p : Fin P.groups.flatten.length → ℂ → ℂ)
    (hP : ∀ u, AnalyticOnNhd ℂ (p u) (closedBall 0 1) ∧ p u 0=0 ∧ p u (r : ℂ)=phasePoint (scannedNode P.groups u))
    {b : ℂ → ℝ} {A : ℝ} (hb : HasPoissonMean r b A)
    (H : ∀ᵐ z ∂poissonLaw r, ‖W.minor i h (fun u => p u z)‖≤exp (b z)) :
    ∃ q : LabelChoice (fun c => (h c).val), ‖W.minor i h (fun u => phasePoint (scannedNode P.groups u))‖≤
      exp (((W.order i : ℝ)-labelPairs (fun c => (q c).val))*log (1/r)+A+1) := by
  have hr' : ‖(r : ℂ)‖=r := by simp [abs_of_pos hr]
  obtain ⟨q,hq⟩ := centered_minor_integral (W.witness i).rowIndex (scannedNode P.groups) (W.frequency i)
    (W.layer i) (centeredGridValue P.shape P.anchor (W.grid i)) h p (fun u => (hP u).1)
    (fun u => (hP u).2.1) (by rw [hr']; exact hr1) hb.1 H
  simp only [(hP _).2.2,hb.2,hr'] at hq
  change ‖W.minor i h (fun u => phasePoint (scannedNode P.groups u))‖≤
    r^(labelPairs (fun c => (q c).val)-W.order i)*exp (A+1) at hq
  refine ⟨q,hq.trans ((mul_le_mul_of_nonneg_right (radius_order_bound hr hr1.le _ _) (exp_pos _).le).trans_eq ?_)⟩
  rw [← exp_add]
  exact congrArg exp (add_assoc _ A 1).symm

theorem angular_sample (i k : ℕ) (hm : ∀ u, 0<(W.witness i).count u ∧ (W.witness i).count u≤W.size i)
    (hN : 2≤W.mass i) {ε : ℝ} (hfit : W.referencesFit k i ε)
    {t : ℝ} (ht : 0≤t) (ht1 : t<1) (g : Fin P.cuts.length → ℂ[X])
    (hg : ∀ j, (g j).eval 0=0 ∧ (∀ x : ℝ, ((g j).eval (x : ℂ)).im=0) ∧ 0<pathGap P.rates.radius (g j))
    {K : ℝ} (hK : 1≤K)
    (hv : ∀ u c, ‖(scannedNode P.groups u : ℂ)-(centeredGridValue P.shape P.anchor (W.grid i) (W.frequency i c) : ℂ)‖≤K)
    (hp : ∀ u (z : ℂ), ‖z‖=1 → ‖incrementFamily P.rates.radius t g (scannedNode P.groups u) z‖≤K)
    (h : LabelChoice (W.layer i)) :
    let r := (P.rates.radius : ℝ)
    let n := W.size i
    let N := W.mass i
    let L := (P.rates.length : ℝ)
    let F (j : Fin P.cuts.length) := P.design.directionForm j.val
    let M := markedMass (fun c => (h c).val) N
    let blocks := ∑ u, blockScaleCost N (innerRadius k) ((W.witness i).count u)
    ∃ q : LabelChoice (fun c => (h c).val), ‖W.minor i h (fun u => phasePoint (scannedNode P.groups u))‖≤exp
      (((W.order i : ℝ)-labelPairs (fun c => (q c).val))*log (1/r)+
       ((n : ℝ)*(log P.groups.flatten.length+columnOverhead K n P.shape.widths.length)+N^2*
        (blocks+L*P.design.energyForm.actual P.rates.radius false+ε-M*P.design.priceForm.actual P.rates.radius false+
         (∫ z, slopeError g F z ∂poissonLaw r)*W.lengthRatio i+correctionMean r t*W.gapTail i (fun j => pathGap r (g j))))+1) := by
  intro r n N L F M blocks
  have hr := P.radius_bounds
  have hr' : ‖(r : ℂ)‖<1 := by simpa [r,abs_of_pos hr.1] using hr.2
  have HA := P.design.face_integrals P.rates.radius hr'
  have hE : HasPoissonMean r P.design.faceEnergy (P.design.energyForm.actual P.rates.radius false) := ⟨HA.1,HA.2.2.1⟩
  have hF : HasPoissonMean r P.design.faceFee (P.design.priceForm.actual P.rates.radius false) := ⟨HA.2.1,HA.2.2.2⟩
  have he : HasPoissonMean r (slopeError g F) (∫ w, slopeError g F w ∂poissonLaw r) := ⟨slopeError_integrable hr' g F,rfl⟩
  have hc : HasPoissonMean r (fun w => |(correctionPath r t w).im|) (correctionMean r t) := ⟨correction_integrable hr' ht ht1,rfl⟩
  have hm₁ := ((((HasPoissonMean.constant hr' blocks).add (hE.left_mul L)).add
    (HasPoissonMean.constant hr' ε)).sub (hF.left_mul M))
  have hm₂ := (hm₁.add (he.right_mul (W.lengthRatio i))).add (hc.right_mul (W.gapTail i (fun j => pathGap r (g j))))
  have hm₃ := (HasPoissonMean.constant hr' ((n : ℝ)*(log P.groups.flatten.length+columnOverhead K n P.shape.widths.length))).add (hm₂.left_mul (N^2))
  apply W.interior_mean i h hr.1 hr.2 _ (P.paths hr.1 ht ht1 g (fun j => (hg j).1)) hm₃
  filter_upwards [poissonLaw_unit r,imaginary_nonzero_ae hr.1 hr.2,Angular_gates_one_ae hr.1 hr.2 P.chain] with z hz hi hθ
  exact W.angular_det_bound i k hm hN hfit hr.1 ht ht1 g (fun j => (hg j).2.1 r)
    (fun j => (hg j).2.2.le) h z hz hi (P.design.weightAt_one _ _ P.valid _ hθ) hK hv (fun u => hp u z hz)

end SelectedSequence
end PiPolynomialValues
