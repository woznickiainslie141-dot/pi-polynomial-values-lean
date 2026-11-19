module

public import OddPiPowers.PolynomialValues.Analysis.AllocatedBlockRate
public import OddPiPowers.PolynomialValues.Analysis.SignedTailBound

/-! Isolate the first moment of each allocated row. Its total absolute
size controls all angular approximation errors, and its signed projection
has the sharper two-sided tail bound from the quantile cuts. -/

@[expose] public section

namespace PiPolynomialValues

open Finset FourPeriod

noncomputable def firstMoment (P : ContinuousCharge FrequencyInterval) := P (linearFrequency 1)

theorem evaluate_linear (P : ContinuousCharge FrequencyInterval) (a : ℝ) :
    P (linearFrequency a)=a*firstMoment P := by
  have h : linearFrequency a=a • linearFrequency 1 := by
    ext x
    change a*(x : ℝ)=a*(1*(x : ℝ))
    ring
  rw [h,map_smul,smul_eq_mul,firstMoment]

theorem allocated_first_sum {n V : ℕ} (m : Fin V → ℕ) (d : ((u : Fin V) × Fin (m u)) ≃ Fin n)
    (y : Fin n → FrequencyInterval) (N : ℝ) (b : Fin V → ℝ) :
    (∑ u, b u*firstMoment (allocationCharge m d y N u))=
      (∑ u, ∑ i : Fin (m u), b u*(y (d ⟨u,i⟩) : ℝ))/N := by
  simp only [firstMoment,allocationCharge,atomicCharge_apply,div_eq_mul_inv,mul_sum,sum_mul]
  exact sum_congr rfl (fun _ _ => sum_congr rfl (fun u _ => by
    change _*(N⁻¹*(1*_))=_*_*N⁻¹
    ring))

theorem allocated_first_abs {n V : ℕ} (m : Fin V → ℕ) (d : ((u : Fin V) × Fin (m u)) ≃ Fin n)
    (y : Fin n → FrequencyInterval) {N : ℝ} (hN : 0<N) :
    (∑ u, |firstMoment (allocationCharge m d y N u)|)≤(n : ℝ)/N := by
  have h (u : Fin V) : |firstMoment (allocationCharge m d y N u)|≤(m u : ℝ)*N⁻¹ := by
    unfold firstMoment allocationCharge
    rw [atomicCharge_apply]
    apply (abs_sum_le_sum_abs _ _).trans
    have hpoint (i : Fin (m u)) : |N⁻¹*(linearFrequency 1) (y (d ⟨u,i⟩))|≤N⁻¹ := by
      change |N⁻¹*(1*(y (d ⟨u,i⟩) : ℝ))|≤N⁻¹
      rw [one_mul,abs_mul,abs_of_pos (inv_pos.mpr hN)]
      exact mul_le_of_le_one_right (inv_pos.mpr hN).le (abs_le.mpr (y _).property)
    exact (sum_le_sum (s := univ) (fun i _ => hpoint i)).trans_eq (by simp)
  have hcard : (∑ u, m u)=n := by simpa [Fintype.card_sigma] using Fintype.card_congr d
  apply (sum_le_sum (fun u _ => h u)).trans_eq
  rw [← sum_mul,← Nat.cast_sum,hcard,div_eq_mul_inv]

theorem allocated_first_tail {n V K : ℕ} (m : Fin V → ℕ) (d : ((u : Fin V) × Fin (m u)) ≃ Fin n)
    (y : Fin n → FrequencyInterval) {N : ℝ} (hN : 0<N) (v : Fin V → ℤ)
    (δ q : Fin K → ℝ) (hδ : ∀ k, 0≤δ k) :
    (∑ u, orderedDirection δ (v u)*firstMoment (allocationCharge m d y N u))≤
      ∑ k, δ k*tailCap m v (fun j => (y j : ℝ)) N k.val (q k) := by
  rw [allocated_first_sum]
  exact allocated_tail_direction m d v (fun j => (y j : ℝ)) hN δ q hδ

end PiPolynomialValues
