module

public import OddPiPowers.PolynomialValues.Analysis.PathApproximation
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Polynomial paths realize an integrable odd boundary field in the
weighted mean. The measure can be any conjugation-invariant probability
supported by the unit circle, including the real-radius Poisson law. -/

@[expose] public section

namespace PiPolynomialValues

open MeasureTheory Complex Metric Filter Polynomial
open scoped ComplexConjugate

theorem integrable_boundary_path {μ : Measure ℂ} [IsProbabilityMeasure μ] [μ.WeaklyRegular]
    (hunit : ∀ᵐ z ∂μ, ‖z‖=1) (hsym : MeasurePreserving (starRingEnd ℂ) μ μ)
    {b : ℂ → ℝ} (hb : Integrable b μ) (hodd : ∀ᵐ z ∂μ, b (conj z) = -b z)
    {ε : ℝ} (hε : 0<ε) :
    ∃ g : ℂ[X], g.eval 0=0 ∧ (∀ x : ℝ, (g.eval (x : ℂ)).im=0) ∧
      (∫ z, |(g.eval z).im-b z| ∂μ) ≤ ε := by
  have hh : 0<ε/2 := by positivity
  obtain ⟨a,ha,hai⟩ := hb.exists_boundedContinuous_integral_sub_le hh
  let A : C(Circle,ℝ) := ⟨fun z => a (z : ℂ),a.continuous.comp continuous_subtype_val⟩
  obtain ⟨g,h0,hr,hg⟩ := exists_real_path_oddpart A hh
  refine ⟨g,h0,hr,?_⟩
  let D (z : ℂ) := |b z-a z|
  have hD : Integrable D μ := (hb.sub hai).norm
  have hD' : Integrable (D ∘ (starRingEnd ℂ)) μ := hsym.integrable_comp_of_integrable hD
  have heq := hsym.integral_comp Complex.conjCLE.toHomeomorph.measurableEmbedding D
  have hupper : Integrable (fun z => ε/2+(D z+D (conj z))/2) μ :=
    (integrable_const _).add ((hD.add hD').div_const 2)
  have H : (∫ z, |(g.eval z).im-b z| ∂μ) ≤ ∫ z, (ε/2+(D z+D (conj z))/2) ∂μ := by
    apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _)) hupper
    filter_upwards [hunit,hodd] with z hz ho
    let s : Circle := ⟨z,mem_sphere_zero_iff_norm.mpr hz⟩
    have he := abs_lt.mp (hg s)
    simp only [A,ContinuousMap.coe_mk,Circle.coe_inv_eq_conj] at he
    change - (ε/2)<(g.eval z).im-(a z-a (conj z))/2 ∧ _<ε/2 at he
    change |(g.eval z).im-b z| ≤ ε/2+(|b z-a z|+|b (conj z)-a (conj z)|)/2
    rw [ho,abs_le]
    constructor <;> linarith only [he.1,he.2,le_abs_self (b z-a z),neg_abs_le (b z-a z),
      le_abs_self (-b z-a (conj z)),neg_abs_le (-b z-a (conj z))]
  apply H.trans
  rw [integral_add (f := fun _ : ℂ => ε/2) (g := fun z => (D z+D (conj z))/2)
    (integrable_const _) ((hD.add hD').div_const 2),integral_const,show μ.real Set.univ=1 by simp [measureReal_def],
    one_smul,integral_div,integral_add (f := D) (g := fun z => D (conj z)) hD hD',heq]
  change (∫ z, D z ∂μ)≤ε/2 at ha
  linarith

end PiPolynomialValues
