module

public import OddPiPowers.PolynomialValues.Analysis.ZeroAllocation

/-! Uniform bound for the reduced value at an arbitrary complex point.
The estimate first controls the original polynomial on the unit circle. -/

@[expose] public section

namespace PiPolynomialValues.SelectedSequence

open FourPeriod Finset Real Filter

variable {P : EvaluationPlan} (W : SelectedSequence P)

noncomputable def nodeBound (P : EvaluationPlan) : ℝ := 1+∑ u, ‖(scannedNode P.groups u : ℂ)‖

theorem nodeBound_one (P : EvaluationPlan) : 1≤nodeBound P :=
  le_add_of_nonneg_right (sum_nonneg (fun _ _ => norm_nonneg _))

theorem nodeBound_ge (P : EvaluationPlan) (u : Fin P.groups.flatten.length) : ‖(scannedNode P.groups u : ℂ)‖≤nodeBound P := by
  exact (single_le_sum (fun j _ => norm_nonneg (scannedNode P.groups j : ℂ)) (mem_univ u)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem unit_estimate (i k : ℕ) (hm : ∀ u, 0<(W.witness i).count u ∧ (W.witness i).count u≤W.size i)
    (hN : 2≤W.mass i) (E : ReferenceEvidence P.shape P.anchor (List.replicate P.shape.ratios.length 0) 0 P.rates.ordinary)
    (z : ℂ) (hz : ‖z‖=1) :
    ‖normalizedDetValue (W.witness i).rows (W.witness i).cols z‖≤exp ((W.size i : ℝ)*
      (log P.groups.flatten.length+columnOverhead (nodeBound P) (W.size i) P.shape.widths.length)+
      (W.mass i)^2*((∑ u, blockScaleCost (W.mass i) (innerRadius k) ((W.witness i).count u))+W.finiteReference E k i)) := by
  let w := W.witness i
  let n := W.size i
  let x (c : Fin n) := (w.colIndex c).2.val
  let j (c : Fin n) := (w.colIndex c).1.val
  let v := scannedNode P.groups
  let p (u : Fin P.groups.flatten.length) (_ : Fin n) := (v u : ℂ)*Complex.I*z/2
  let A (u : Fin P.groups.flatten.length) (c : Fin n) := (2 : ℂ)^(j c)*Complex.I^(v u*x c)
  have hA (u c) : ‖A u c‖=(2 : ℝ)^j c := by simp [A,norm_zpow]
  have hp (u c) : ‖p u c‖≤nodeBound P := by
    simpa only [p,norm_div,norm_mul,Complex.norm_I,hz,mul_one,Complex.norm_ofNat] using
      (div_le_self (norm_nonneg (v u : ℂ)) (by norm_num : (1 : ℝ)≤2)).trans (nodeBound_ge P u)
  obtain ⟨θ,hθ⟩ := unit_allocated_rate w.rowIndex P.groups_pos hm x j (fun c => (w.colIndex c).1.isLt.le)
    p A hA (nodeBound_one P) hp hN (innerRadius_bounds k).1 (innerRadius_bounds k).2 (W.columns i false)
    (fun c => W.columns_value (by linarith) false c)
  have hR := W.zero_reference_bound k i (by linarith) E false (allocationEquiv w.rowIndex θ)
  rw [w.unit_path_matrix]
  apply hθ.trans
  rw [exp_le_exp]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [sum_add_distrib]
  exact add_le_add le_rfl hR

theorem unit_uniform {ε : ℝ} (hε : 0<ε) : ∀ᶠ i in atTop, ∀ z : ℂ,
    reducedEvaluation (W.witness i).integral z≤((W.witness i).denominator : ℝ)*exp ((W.mass i)^2*
      ((P.rates.length : ℝ)*((P.rates.baseCost : ℝ)+P.rates.ordinary)+ε)) := by
  let E := Classical.choice P.zeroRate
  have he : 0<ε/3 := by positivity
  obtain ⟨k,hb,hr⟩ := ((W.block_fit he).and (W.reference_eventual E he)).exists
  have ho := (W.overhead_limit (nodeBound P) (nodeBound_one P) P.shape.widths.length P.groups.flatten.length).eventually
    (gt_mem_nhds he)
  filter_upwards [hb,hr,ho,W.positive_rows,W.mass_atTop.eventually (eventually_ge_atTop 2)] with i hB hR hO hm hN
  intro z
  apply (W.witness i).reduced_eval_of_unit_bound _ z
  intro ζ hζ
  apply (W.unit_estimate i k hm hN E ζ hζ).trans
  rw [exp_le_exp]
  have hpos : 0<(W.mass i)^2 := sq_pos_of_pos (by linarith)
  have hO' := (div_lt_iff₀ hpos).mp hO
  have hS := mul_le_mul_of_nonneg_left (add_le_add hB hR.le) hpos.le
  linarith only [hO',hS]

theorem prime_rate : UpperRate atTop
    (fun i => log ((W.witness i).denominator : ℝ)/((W.size i : ℝ)*W.mass i)) (P.rates.primeCost : ℝ) := by
  intro ε hε
  filter_upwards [W.index_atTop.eventually (P.primes ε hε),W.mass_atTop.eventually (eventually_ge_atTop 2)] with i h hN
  have hpos : 0<W.mass i := by linarith
  have hw : (P.shape.totalWidthQ : ℝ)*W.mass i≤(W.size i : ℝ) := card_ge_width_mass P.shape (W.index i)
  rw [P.width_eq] at hw
  have hs := (mul_pos P.length_pos hpos).trans_le hw
  apply (div_le_iff₀ (mul_pos hs hpos)).mpr
  have hh := h P.degreeA P.degreeB (W.root i) (W.witness i)
  change log ((W.witness i).denominator : ℝ)≤((P.rates.primeCost : ℝ)+ε)*(W.size i : ℝ)*W.mass i at hh
  exact hh.trans_eq (mul_assoc _ _ _)

end PiPolynomialValues.SelectedSequence
