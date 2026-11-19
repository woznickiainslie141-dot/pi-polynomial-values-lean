module

public import OddPiPowers.PolynomialValues.Analysis.LabelOrderDeterminant
public import OddPiPowers.PolynomialValues.PricedSimplex
public import Mathlib.Data.Nat.Choose.Cast

/-! The priced simplex acts on the finite Taylor-label multiplicities
of the determinant. Both the exponent and the off-center count use
the actual perturbation labels before the Taylor expansion. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

def finiteLabelCount {n J : ℕ} (q : Fin n → Fin J) (k : Fin J) :=
  (univ.filter (fun i => q i=k)).card

theorem finiteLabelCount_sum {n J : ℕ} (q : Fin n → Fin J) : ∑ k, finiteLabelCount q k=n := by
  have H := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ) (f := q)
    (fun i _ => mem_univ _)
  simpa [finiteLabelCount] using H.symm

theorem labelPairs_finite {n J : ℕ} (q : Fin n → Fin J) :
    labelPairs (fun c => (q c).val) = ∑ k, (finiteLabelCount q k).choose 2 := by
  let f (k : ℕ) := (univ.filter (fun i => (q i).val=k)).card.choose 2
  have he : labelPairs (fun c => (q c).val) = ∑ k ∈ range J, f k := by
    apply sum_subset
    · exact fun k hk => by obtain ⟨i,_,rfl⟩ := mem_image.mp hk; exact mem_range.mpr (q i).isLt
    · intro k _ hk
      have hn : ∀ i, (q i).val≠k := fun i hi => hk (mem_image.mpr ⟨i,mem_univ _,hi⟩)
      simp [f,hn]
  rw [he,← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro k _
  simp [f,finiteLabelCount,Fin.val_inj]

theorem finiteLabelCount_squares {n J : ℕ} (q : Fin n → Fin J) :
    (∑ k, (finiteLabelCount q k : ℝ)^2) = 2*labelPairs (fun c => (q c).val)+n := by
  have hc : (n : ℝ)=∑ i, (finiteLabelCount q i : ℝ) := by rw [← Nat.cast_sum,finiteLabelCount_sum]
  rw [labelPairs_finite,Nat.cast_sum,mul_sum,hc,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [Nat.cast_choose_two]
  ring

theorem price_per_column {n J : ℕ} (q : Fin n → Fin J) (c δ : ℝ) :
    (∑ k, labelPrice c δ k.val*(finiteLabelCount q k : ℝ)) = ∑ i, labelPrice c δ (q i).val := by
  rw [← sum_fiberwise_of_maps_to (s := (univ : Finset (Fin n))) (t := univ) (g := q)
    (fun _ _ => mem_univ _) (fun i => labelPrice c δ (q i).val)]
  apply sum_congr rfl
  intro k _
  rw [sum_congr rfl (fun i hi => congrArg (fun j : Fin J => labelPrice c δ j.val) (mem_filter.mp hi).2)]
  simp [finiteLabelCount,mul_comm]

theorem finite_priced_origin {n J : ℕ} (hn : 0 < n) (q : Fin n → Fin (J+2)) (h : Fin n → ℕ)
    (hqh : ∀ i, (q i).val ≤ h i) {B c δ : ℝ} (hB : 0<B) (hc : 0≤c) (hδ : 0≤δ) (hhi : 2*B≤3*c+δ) :
    pricedMinimum B c δ ≤
      (∑ i, ((h i : ℝ)*c+(if h i=0 then 0 else δ)))/n+
        B*(2*labelPairs (fun i => (q i).val)+(n : ℝ))/(n : ℝ)^2 := by
  let p (k : Fin (J+2)) := (finiteLabelCount q k : ℝ)/n
  have hnp : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hs : ∑ k, p k=1 := by
    simp only [p,div_eq_mul_inv,← sum_mul,← Nat.cast_sum,finiteLabelCount_sum,mul_inv_cancel₀ hnp]
  have hp := priced_simplex_bound B c δ hB hc hhi p (fun _ => by dsimp [p]; positivity) hs
  have H (i : Fin n) : labelPrice c δ (q i).val ≤ ((h i : ℝ)*c+(if h i=0 then 0 else δ)) := by
    have hm := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).mpr (hqh i)) hc
    cases hs : (q i).val with
    | zero => simp only [hs,Nat.cast_zero,zero_mul] at hm; simp only [labelPrice]; split <;> linarith
    | succ k =>
      have hz : h i ≠ 0 := by have := hqh i; omega
      simp only [labelPrice,hz,if_false,Nat.cast_succ,hs] at hm ⊢
      linarith
  apply hp.trans
  have h1 (k : Fin (J+2)) : labelPrice c δ k.val*p k =
      (labelPrice c δ k.val*(finiteLabelCount q k : ℝ))*(n : ℝ)⁻¹ := by dsimp [p]; ring
  have h2 (k : Fin (J+2)) : B*(p k)^2 =
      (B*(finiteLabelCount q k : ℝ)^2)*((n : ℝ)^2)⁻¹ := by
    simp only [p,div_eq_mul_inv,mul_pow,inv_pow]
    ring
  conv_lhs =>
    rw [sum_add_distrib]
    simp only [h1,h2,← sum_mul,← mul_sum]
    rw [price_per_column,finiteLabelCount_squares]
    simp only [← div_eq_mul_inv]
  exact add_le_add (div_le_div_of_nonneg_right (sum_le_sum (fun i _ => H i)) (Nat.cast_nonneg n)) (le_of_eq (by ring))

end PiPolynomialValues.FourPeriod
