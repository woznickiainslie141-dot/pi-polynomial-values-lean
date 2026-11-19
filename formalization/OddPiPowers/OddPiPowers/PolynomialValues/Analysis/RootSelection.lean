module

public import OddPiPowers.PolynomialValues.Analysis.EvaluationScale
public import OddPiPowers.PolynomialValues.ConjugateTaylorDecay

/-! The principal conjugate is eventually real. The minor can be
selected at every index while agreeing with this conjugate eventually.
The resultant then makes all reduced conjugate evaluations positive. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Filter Finset Polynomial Real
open scoped Topology

theorem capped_lt_raw {ξ z u : ℂ} {C X : ℝ} (h : cappedProximity C X ξ z<cappedProximity C X ξ u) :
    rootProximity ξ z<rootProximity ξ u := by
  by_contra! hh
  apply h.not_ge
  exact min_le_min_left _ (div_le_div_of_nonneg_right hh (zero_le_one.trans (le_max_left _ _)))

theorem principal_real_eventually {k : ℕ} (p : ℕ → ℤ[X]) (hd : ∀ i, (p i).natDegree=k+1)
    (hn : ∀ i, ∀ z∈((p i).map (Int.castRingHom ℂ)).roots, (π : ℂ)≠z)
    (X : ℕ → ℝ) {C : ℝ} (b : Fin (k+1) → ℝ)
    (h : ∀ j, Tendsto (fun i => cappedProximity C (X i) π (indexedRoot (p i) π (hd i) j)) atTop (𝓝 (b j)))
    (gap : ∀ j : Fin k, b j.succ<b 0) :
    ∀ᶠ i in atTop, ∃ x : ℝ, indexedRoot (p i) π (hd i) 0=(x : ℂ) := by
  have all := eventually_all.mpr (fun j : Fin k => (h j.succ).eventually_lt (h 0) (gap j))
  filter_upwards [all] with i hi
  exact principal_real_of_gap (p i) π (hd i) (hn i) (fun j => capped_lt_raw (hi j))

noncomputable def selectAtRoots (P : EvaluationPlan) (z : ℕ → ℂ) (X : ℕ → ℝ) (hX : Tendsto X atTop atTop) :
    SelectedSequence P where
  grid i := ⌊((P.rates.scale : ℝ)/(4*P.shape.massUnit))*X i⌋₊
  grow := tendsto_nat_floor_atTop.comp (hX.const_mul_atTop (div_pos P.degree_scale_pos
    (mul_pos (by norm_num) (Nat.cast_pos.mpr P.rows.mass_pos))))
  root i := if z i=0 then 1 else z i
  witness i := Classical.choice (P.select _ _ (by split <;> simp_all))

noncomputable def scaleAtRoots (P : EvaluationPlan) (z : ℕ → ℂ) (X : ℕ → ℝ) (hX : Tendsto X atTop atTop) :
    EvaluationScale (selectAtRoots P z X hX) where
  X := X
  grow := hX
  ratio := rootScaleIndex_ratio hX P.shape P.rows.mass_pos P.degree_scale_pos

theorem real_root_resultant {k : ℕ} {P : EvaluationPlan} (W : SelectedSequence P)
    (p : ℕ → ℤ[X]) (hd : ∀ i, (p i).natDegree=k+1)
    (hirr : ∀ i, Irreducible ((p i).map (Int.castRingHom ℚ)))
    (he : ∀ᶠ i in atTop, W.root i=indexedRoot (p i) π (hd i) 0)
    (hr : ∀ᶠ i in atTop, ∃ x : ℝ, indexedRoot (p i) π (hd i) 0=(x : ℂ)) :
    ∀ᶠ i in atTop, (∀ j, 0<reducedEvaluation (W.witness i).integral (indexedRoot (p i) π (hd i) j)) ∧
      0≤((W.witness i).integral.natDegree : ℝ)*log (measure (p i))+
        ∑ j, log (reducedEvaluation (W.witness i).integral (indexedRoot (p i) π (hd i) j)) := by
  filter_upwards [he,hr] with i hw hr'
  obtain ⟨x,hx⟩ := hr'
  let z := indexedRoot (p i) (π : ℂ) (hd i)
  let R := (W.witness i).integral
  have hf := isRoot_of_mem_roots (indexed_root_mem (p i) (π : ℂ) (hd i) 0)
  change ((p i).map (Int.castRingHom ℂ)).eval (indexedRoot (p i) π (hd i) 0)=0 at hf
  rw [hx,eval_map] at hf
  have hR : R.eval₂ GaussianInt.toComplex (x : ℂ)≠0 := fun hzero =>
    (W.witness i).eval_ne ((congrArg (fun z : ℂ => R.eval₂ GaussianInt.toComplex z) (hw.trans hx)).trans hzero)
  have H := one_le_reduced_resultant (p i) R x (hirr i) hf hR
  have hlog := log_resultant_obstruction (p i) R x (hirr i) hf hR
  rw [sum_indexed_roots (p i) (π : ℂ) (hd i)] at hlog
  refine ⟨fun j => ?_,hlog⟩
  have hprod := right_ne_zero_of_mul (zero_lt_one.trans_le H).ne'
  have hval : reducedEvaluation R (z j)≠0 := by
    intro he'
    apply hprod
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨z j,indexed_root_mem _ _ _ j,he'⟩)
  exact lt_of_le_of_ne (div_nonneg (norm_nonneg _) (pow_nonneg (rootScale_pos _).le _)) hval.symm

end PiPolynomialValues
