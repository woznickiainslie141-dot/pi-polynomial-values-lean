module

public import OddPiPowers.PolynomialValues.Analysis.FixedResidual
public import OddPiPowers.PolynomialValues.Analysis.AtomicPotential

/-! Finite dual bound for the actual allocated columns. The right side
keeps one price per column, the exact row counts, and a fixed residual test. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {n V : ℕ} (m : Fin V → ℕ)

noncomputable def allocationCharge (d : ((v : Fin V) × Fin (m v)) ≃ Fin n)
    (y : Fin n → X) (N : ℝ) (v : Fin V) : ContinuousCharge X :=
  atomicCharge (fun i => y (d ⟨v,i⟩)) (fun _ => N⁻¹)

theorem allocation_linear_bound (d : ((v : Fin V) × Fin (m v)) ≃ Fin n)
    (y : Fin n → X) {N : ℝ} (hN : 0<N) (f g : Fin V → C(X,ℝ)) (β : Fin V → ℝ)
    (price : Fin n → ℝ) (he : ∀ v i, f v (y (d ⟨v,i⟩))+g v (y (d ⟨v,i⟩)) ≤ price (d ⟨v,i⟩)+β v) :
    (∑ v, (allocationCharge m d y N v (f v)+allocationCharge m d y N v (g v))) ≤
      N⁻¹*(∑ c, price c)+∑ v, (m v : ℝ)/N*β v := by
  have h (v : Fin V) : allocationCharge m d y N v (f v)+allocationCharge m d y N v (g v) ≤
      (∑ i : Fin (m v), N⁻¹*price (d ⟨v,i⟩))+(m v : ℝ)/N*β v := by
    have H := sum_le_sum (s := (univ : Finset (Fin (m v)))) (fun i _ =>
      mul_le_mul_of_nonneg_left (he v i) (inv_nonneg.mpr hN.le))
    simp only [mul_add,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at H
    simpa only [allocationCharge,atomicCharge_apply,div_eq_mul_inv,mul_assoc] using H
  have H := sum_le_sum (s := (univ : Finset (Fin V))) (fun v _ => h v)
  have heq := d.sum_comp (fun c => N⁻¹*price c)
  rw [Fintype.sum_sigma,← mul_sum] at heq
  simpa only [sum_add_distrib,heq] using H

theorem allocation_energy_bound (hV : 0<V) (d : ((v : Fin V) × Fin (m v)) ≃ Fin n)
    (y : Fin n → X) {N : ℝ} (hN : 0<N) (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖=1)
    {r : ℝ} (hr : 0≤r) (hr1 : r<1) (Q : Fin V → ContinuousCharge X) (ν : ContinuousCharge X)
    (f : Fin V → C(X,ℝ)) (β : Fin V → ℝ) (price : Fin n → ℝ)
    (he : ∀ v i, f v (y (d ⟨v,i⟩))+radialPotential u r (Q v) (y (d ⟨v,i⟩)) ≤ price (d ⟨v,i⟩)+β v) :
    let P := allocationCharge m d y N
    let S := ν-∑ v, Q v
    (∑ v, (P v (f v)+radialInteraction u r (P v) (P v)/2)) ≤
      N⁻¹*(∑ c, price c)+(∑ v, ((m v : ℝ)/N*β v-radialInteraction u r (Q v) (Q v)/2))+
      (2*((∑ v, P v)-ν) (radialPotential u r S)+radialInteraction u r S S)/(2*V) := by
  intro P S
  have H := radial_dual_fixed hV u hu hr hr1 P Q ν
  have A := allocation_linear_bound m d y hN f (fun v => radialPotential u r (Q v)) β price he
  change (∑ v, (P v (f v)+P v (radialPotential u r (Q v)))) ≤ _ at A
  dsimp only at H
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,div_eq_mul_inv,← sum_mul] at H A ⊢
  change (∑ v, P v (f v))+(∑ v, radialInteraction u r (P v) (P v))*2⁻¹ ≤ _
  have heq (x : ℝ) : x*(2*(V : ℝ))⁻¹=(x*(V : ℝ)⁻¹)/2 := by rw [mul_inv_rev]; ring
  rw [heq]
  linarith only [H,A]

end PiPolynomialValues
