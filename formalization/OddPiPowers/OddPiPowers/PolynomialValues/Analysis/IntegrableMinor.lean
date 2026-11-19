module

public import OddPiPowers.PolynomialValues.Analysis.MeasurablePathBound
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A lower truncation of an integrable boundary majorant changes its
Poisson average by arbitrarily little. This avoids a uniform lower bound
on the angular approximation as its polynomial degree increases. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open MeasureTheory Metric Set Filter Real
open scoped Topology

theorem lower_truncation_mean {r : ℝ} (hr : ‖(r : ℂ)‖<1) {b : ℂ → ℝ} (hb : Integrable b (poissonLaw r)) :
    Tendsto (fun n : ℕ => ∫ z, max (-(n : ℝ)) (b z) ∂poissonLaw r) atTop (𝓝 (∫ z, b z ∂poissonLaw r)) := by
  letI := poissonLaw_probability hr
  have H (n : ℕ) : Integrable (fun z => max (-(n : ℝ)) (b z)) (poissonLaw r) :=
    (integrable_const (-(n : ℝ))).sup hb
  apply tendsto_integral_of_dominated_convergence (fun z => |b z|) (fun n => (H n).aestronglyMeasurable) hb.abs
  · intro n
    apply Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨(neg_abs_le (b z)).trans (le_max_right _ _),max_le (by linarith [Nat.cast_nonneg (α := ℝ) n,abs_nonneg (b z)]) (le_abs_self _)⟩
  · apply Eventually.of_forall
    intro z
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (-(b z)))] with n hn
    exact (max_eq_right (by linarith : -(n : ℝ)≤b z)).symm

theorem centered_minor_integral {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ → ℂ) (hp : ∀ i, AnalyticOnNhd ℂ (p i) (closedBall 0 1)) (h0 : ∀ i, p i 0=0)
    {r : ℝ} (hr : ‖(r : ℂ)‖<1) {b : ℂ → ℝ} (hb : Integrable b (poissonLaw r))
    (hbound : ∀ᵐ z ∂poissonLaw r, ‖(centeredLabelMatrix e v x j a h (fun i => p i z)).det‖≤exp (b z)) :
    ∃ q : LabelChoice (fun c => (h c).val), ‖(centeredLabelMatrix e v x j a h (fun i => p i (r : ℂ))).det‖≤
      ‖(r : ℂ)‖^(labelPairs (fun c => (q c).val)-∑ i, (e i).2.val)*exp ((∫ z, b z ∂poissonLaw r)+1) := by
  letI := poissonLaw_probability hr
  obtain ⟨k,hk⟩ := ((lower_truncation_mean hr hb).eventually (gt_mem_nhds (lt_add_one _))).exists
  have hi : Integrable (fun z => max (-(k : ℝ)) (b z)) (poissonLaw r) := (integrable_const (-(k : ℝ))).sup hb
  obtain ⟨q,hq⟩ := centered_path_integral e v x j a h p hp h0 hr hi
    (Eventually.of_forall (fun z => le_max_left (-(k : ℝ)) (b z)))
    (hbound.mono (fun z h => h.trans (exp_le_exp.mpr (le_max_right _ _))))
  exact ⟨q,hq.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hk.le) (by positivity))⟩

end PiPolynomialValues.FourPeriod
