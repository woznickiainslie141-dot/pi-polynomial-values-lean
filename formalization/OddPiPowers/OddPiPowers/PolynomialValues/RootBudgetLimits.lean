module

public import OddPiPowers.PolynomialValues.OrderedRootInputs

/-! The secondary logarithmic exponents have total at most the actual
degree minus one. The principal exponent supplies the remaining target,
and the strict gap forces its conjugate to be real. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Filter Real Polynomial
open scoped Topology

theorem capped_root_budgets {k : ℕ} (z : ℕ → Fin (k+1) → ℂ) (ξ : ℂ) (X : ℕ → ℝ) (hX : Tendsto X atTop atTop)
    (C A B : ℝ) (hC : (k : ℝ)<C) (hA : 0≤A) (hB : 0≤B)
    (ht : ∀ i, C*X i-A≤∑ j, rootProximity ξ (z i j))
    (hs : ∀ i, (∑ j : Fin k, rootProximity ξ (z i j.succ))≤(k : ℝ)*X i+B) :
    ∃ b : Fin (k+1) → ℝ, (∀ j, 0≤b j ∧ b j≤C) ∧
      (∑ j : Fin k, b j.succ)≤k ∧ C-(∑ j : Fin k, b j.succ)≤b 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, Tendsto (fun i => cappedProximity C (X (φ i)) ξ (z (φ i) j)) atTop (𝓝 (b j)) := by
  let S (i : ℕ) := ∑ j : Fin k, rootProximity ξ (z i j.succ)
  have hC₀ : 0≤C := (Nat.cast_nonneg k).trans hC.le
  obtain ⟨b,hb,φ,hφ,H⟩ := subseq_cappedProximity z ξ X hC₀
  have hX' := hX.comp hφ.tendsto_atTop
  have hx : ∀ᶠ i in atTop, 1≤X (φ i) := hX'.eventually (eventually_ge_atTop 1)
  have hlow : ∀ i, 0≤S i := fun i => sum_nonneg (fun _ _ => rootProximity_nonneg _ _)
  have Hinv : Tendsto (fun i => (X (φ i))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hX'
  have hK : Tendsto (fun i => B/X (φ i)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using Hinv.const_mul B
  have hJ : Tendsto (fun i => A/X (φ i)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using Hinv.const_mul A
  have hS : ∀ᶠ i in atTop, S (φ i)/X (φ i)≤(k : ℝ)+B/X (φ i) := by
    filter_upwards [hx] with i hi
    have hx' := zero_lt_one.trans_le hi
    apply (div_le_iff₀ hx').mpr
    rw [add_mul,div_mul_cancel₀ _ hx'.ne']
    exact hs (φ i)
  have hcap : ∀ᶠ i in atTop, ∀ j : Fin k, cappedProximity C (X (φ i)) ξ (z (φ i) j.succ)=
      rootProximity ξ (z (φ i) j.succ)/X (φ i) := by
    filter_upwards [hx,hS,hK.eventually (gt_mem_nhds (sub_pos.mpr hC))] with i hi hs' hk
    intro j
    have h := single_le_sum (s := univ) (f := fun j : Fin k => rootProximity ξ (z (φ i) j.succ))
      (fun _ _ => rootProximity_nonneg _ _) (mem_univ j)
    have h' := (div_le_div_of_nonneg_right h (zero_le_one.trans hi)).trans hs'
    unfold cappedProximity
    rw [max_eq_right hi,min_eq_right (by linarith)]
  have hsum : Tendsto (fun i => S (φ i)/X (φ i)) atTop (𝓝 (∑ j : Fin k, b j.succ)) := by
    apply (tendsto_finsetSum univ (fun j _ => H j.succ)).congr'
    filter_upwards [hcap] with i hi
    simp only [hi,S,sum_div]
  have hS' : (∑ j : Fin k, b j.succ)≤k := by
    have hk := hK.const_add (k : ℝ)
    simp only [add_zero] at hk
    exact le_of_tendsto_of_tendsto hsum hk hS
  have hP : ∀ᶠ i in atTop, C-S (φ i)/X (φ i)-A/X (φ i)≤cappedProximity C (X (φ i)) ξ (z (φ i) 0) := by
    filter_upwards [hx] with i hi
    unfold cappedProximity
    rw [max_eq_right hi]
    apply cutoff_principal (zero_lt_one.trans_le hi) (hlow _) hA
    simpa only [S,Fin.sum_univ_succ] using ht (φ i)
  have hL := (hsum.const_sub C).sub hJ
  simp only [sub_zero] at hL
  exact ⟨b,hb,hS',le_of_tendsto_of_tendsto hL (H 0) hP,φ,hφ,H⟩

theorem primitive_root_budgets {d k : ℕ} (p : ℕ → ℤ[X]) (hd : ∀ i, (p i).natDegree=k+1)
    (H : ∀ i, PrimitiveInput d (p i)) (hd3 : d≤3) (hh : Tendsto (fun i => height (p i)) atTop atTop)
    {w : ℝ} (hw : 0≤w) (hC : (k : ℝ)<1+w) (hsmall : ∀ i, |value π (p i)|<(height (p i) : ℝ)^(-w)) :
    let z i := indexedRoot (p i) (π : ℂ) (hd i)
    let X i := log (measure (p i))
    ∃ b : Fin (k+1) → ℝ, (∀ j, 0≤b j ∧ b j≤1+w) ∧
      (∑ j : Fin k, b j.succ)≤k ∧ 1+w-(∑ j : Fin k, b j.succ)≤b 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, Tendsto (fun i => cappedProximity (1+w) (X (φ i)) π (z (φ i) j)) atTop (𝓝 (b j)) := by
  intro z X
  have hne (i : ℕ) : p i≠0 := by have h := (H i).2.2.1; intro he; simp [he] at h
  have hdeg (i : ℕ) := (H i).2.2.2.trans hd3
  apply capped_root_budgets z π X (tendsto_log_atTop.comp (measure_tendsto_of_height p (fun i => (H i).2.2.2) hh))
    (1+w) (w*log ((d : ℝ)+1)) (3*log (2*(1+‖(π : ℂ)‖))) hC
    (mul_nonneg hw (log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) d]))) (by apply mul_nonneg (by norm_num); apply log_nonneg; linarith [norm_nonneg (π : ℂ)])
  · intro i
    have h := small_value_budget (p i) (hne i) (H i).2.2.2 hw (pi_cubic_value_ne_zero _ (hne i) (hdeg i)) (hsmall i)
    rw [sum_indexed_roots _ (π : ℂ) (hd i)] at h
    exact h
  · intro i
    exact secondary_indexed_budget (p i) π (hd i) (hdeg i) (H i).2.1 (fun y hy => pi_not_integer_root _ (hne i) (hdeg i) hy)

end PiPolynomialValues
