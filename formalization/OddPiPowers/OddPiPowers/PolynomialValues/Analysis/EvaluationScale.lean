module

public import OddPiPowers.PolynomialValues.Analysis.UnitEvaluations

/-! Translate the natural mass and column normalizations into the
logarithmic Mahler-measure scale along the selected sequence. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Finset Filter Real
open scoped Topology

theorem UpperRate.of_relaxed {ι : Type*} {F : Filter ι} {f : ι → ℝ} {A K : ℝ}
    (h : ∀ η>0, UpperRate F f (A+K*η)) : UpperRate F f A := by
  intro ε hε
  let η := ε/(2*(|K|+1))
  have hη : 0<η := by dsimp only [η]; positivity
  have he : 2*(|K|+1)*η=ε := by dsimp only [η]; field_simp
  filter_upwards [h η hη η hη] with i hi
  nlinarith only [hi,he,mul_le_mul_of_nonneg_right (le_abs_self K) hη.le,hη.le,mul_nonneg (abs_nonneg K) hη.le]

namespace SelectedSequence

variable {P : EvaluationPlan} (W : SelectedSequence P)

theorem width_le_size (i : ℕ) : (P.rates.length : ℝ)*W.mass i≤(W.size i : ℝ) := by
  rw [← P.width_eq]
  exact card_ge_width_mass P.shape (W.index i)

theorem size_atTop : Tendsto (fun i => (W.size i : ℝ)) atTop atTop :=
  tendsto_atTop_mono W.width_le_size (W.mass_atTop.const_mul_atTop P.length_pos)

theorem degree_rate : UpperRate atTop (fun i => ((W.witness i).integral.natDegree : ℝ)/(W.size i : ℝ))
    (P.rates.auxDegree : ℝ) := by
  have hw : 0<P.shape.widths.sum := by
    by_contra! h
    have he : P.shape.widths.sum=0 := Nat.eq_zero_of_le_zero h
    have hv := (of_decide_eq_true P.base).1
    simp [Shape.totalWidthQ,he] at hv
  have H := (affine_ratio_atTop P.degreeA P.degreeB (2*P.shape.widths.sum*P.shape.rows.sum) P.shape.widths.length
    (Nat.mul_pos (Nat.mul_pos (by decide) hw) P.rowSum_pos)).comp W.index_atTop
  simp only [Function.comp_def,← shape_column_card] at H
  apply (UpperRate.of_tendsto H).mono
    (Eventually.of_forall (fun i => div_le_div_of_nonneg_right (Nat.cast_le.mpr (W.witness i).degree_le)
      (Nat.cast_nonneg (α := ℝ) (W.size i))))
  apply le_of_eq
  rw [← P.degree_ratio]
  simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Nat.cast_mul,Nat.cast_ofNat]

end SelectedSequence

structure EvaluationScale {P : EvaluationPlan} (W : SelectedSequence P) where
  X : ℕ → ℝ
  grow : Tendsto X atTop atTop
  ratio : Tendsto (fun i => W.mass i/X i) atTop (𝓝 (P.rates.scale : ℝ))

namespace EvaluationScale

variable {P : EvaluationPlan} {W : SelectedSequence P} (S : EvaluationScale W)

noncomputable def normRate (v : ℕ → ℝ) (i : ℕ) := v i/((W.size i : ℝ)*S.X i)

theorem positive : ∀ᶠ i in atTop, 0<S.X i ∧ 0<W.mass i ∧ 0<(W.size i : ℝ) :=
  (S.grow.eventually (eventually_gt_atTop 0)).and ((W.mass_atTop.eventually (eventually_gt_atTop 0)).and
    (W.size_atTop.eventually (eventually_gt_atTop 0)))

theorem columns_ratio : Tendsto (fun i => (W.size i : ℝ)/S.X i) atTop
    (𝓝 ((P.rates.length : ℝ)*P.rates.scale)) := by
  apply (W.length_limit.mul S.ratio).congr'
  filter_upwards [S.positive] with i hi
  change ((W.size i : ℝ)/W.mass i)*(W.mass i/S.X i)=_
  field_simp [hi.1.ne',hi.2.1.ne']

theorem mass_factor : Tendsto (S.normRate (fun i => (W.mass i)^2)) atTop
    (𝓝 ((P.rates.scale : ℝ)/P.rates.length)) := by
  apply (S.ratio.div W.length_limit P.length_pos.ne').congr'
  filter_upwards [S.positive] with i hi
  change W.mass i/S.X i/((W.size i : ℝ)/W.mass i)=(W.mass i)^2/((W.size i : ℝ)*S.X i)
  field_simp [hi.1.ne',hi.2.1.ne',hi.2.2.ne']

theorem scaled_prime : UpperRate atTop (S.normRate (fun i => log ((W.witness i).denominator : ℝ)))
    ((P.rates.scale : ℝ)*P.rates.primeCost) := by
  have hp := W.prime_rate.mul_scale S.ratio (S.positive.mono (fun i h => div_nonneg h.2.1.le h.1.le)) P.degree_scale_pos.le
  apply hp.mono _ le_rfl
  filter_upwards [S.positive] with i hi
  apply le_of_eq
  unfold normRate
  field_simp [hi.1.ne',hi.2.1.ne',hi.2.2.ne']
  <;> ring

theorem log_unit {z : ℕ → ℂ} (hz : ∀ᶠ i in atTop, 0<reducedEvaluation (W.witness i).integral (z i)) :
    UpperRate atTop (S.normRate (fun i => log (reducedEvaluation (W.witness i).integral (z i))))
      ((P.rates.scale : ℝ)*((P.rates.primeCost : ℝ)+P.rates.baseCost+P.rates.ordinary)) := by
  apply UpperRate.of_relaxed (K := (P.rates.scale : ℝ)/P.rates.length)
  intro η hη
  let A := (P.rates.length : ℝ)*((P.rates.baseCost : ℝ)+P.rates.ordinary)+η
  have H := S.scaled_prime.add (UpperRate.of_tendsto (S.mass_factor.mul_const A))
  apply H.mono
  · filter_upwards [S.positive,W.unit_uniform hη,hz] with i hi hU hv
    have hd : 0<((W.witness i).denominator : ℝ) := by exact_mod_cast (W.witness i).denominator_pos
    have hb := log_le_log hv (hU (z i))
    rw [log_mul hd.ne' (exp_pos _).ne',log_exp] at hb
    have hn := div_le_div_of_nonneg_right hb (mul_nonneg hi.2.2.le hi.1.le)
    exact hn.trans_eq (by dsimp only [normRate,A]; ring)
  · apply le_of_eq
    dsimp only [A]
    field_simp [P.length_pos.ne']
    <;> ring

end EvaluationScale
end PiPolynomialValues
