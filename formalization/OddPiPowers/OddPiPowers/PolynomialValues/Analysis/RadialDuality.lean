module

public import OddPiPowers.PolynomialValues.Analysis.RadialPotential
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! A simultaneous dual energy inequality including the total residual
charge. This keeps the signed correction used by both numeric shapes. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem radialInteraction_nonpos (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (P : ContinuousCharge X) : radialInteraction u r P P ≤ 0 := by
  apply le_of_tendsto (radialInteraction_hasSum u hu hr hr1 P P)
  filter_upwards with F
  apply sum_nonpos
  intro k _
  have hw : 0 ≤ radialFourierWeight r k := by unfold radialFourierWeight; positivity
  rw [mul_assoc (-2*radialFourierWeight r k),← sq]
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hw) (sq_nonneg _)

theorem radial_dual_residual {V : ℕ} (hV : 0 < V) (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (P Q : Fin V → ContinuousCharge X) :
    (∑ i, radialInteraction u r (P i) (P i)) ≤
      (∑ i, (2*radialInteraction u r (P i) (Q i)-radialInteraction u r (Q i) (Q i))) +
        radialInteraction u r (∑ i : Fin V, (P i-Q i)) (∑ i : Fin V, (P i-Q i))/V := by
  let T := unitMoment u
  let a (k : ℕ) := -2*radialFourierWeight r k
  let d (k : ℕ) (i : Fin V) := P i (T k)-Q i (T k)
  let R : ContinuousCharge X := ∑ i : Fin V, (P i-Q i)
  have hR (k : ℕ) : R (T k) = ∑ i, d k i := by simp [R,d]
  have h₁ := hasSum_sum (s := (univ : Finset (Fin V)))
    (fun i _ => radialInteraction_hasSum u hu hr hr1 (P i) (P i))
  have h₂ := hasSum_sum (s := (univ : Finset (Fin V)))
    (fun i _ => ((radialInteraction_hasSum u hu hr hr1 (P i) (Q i)).mul_left 2).sub
      (radialInteraction_hasSum u hu hr hr1 (Q i) (Q i)))
  have h₃ := (radialInteraction_hasSum u hu hr hr1 R R).div_const (V : ℝ)
  apply hasSum_le _ h₁ (h₂.add h₃)
  intro k
  change (∑ i, a k*P i (T k)*P i (T k)) ≤
    (∑ i, (2*(a k*P i (T k)*Q i (T k))-a k*Q i (T k)*Q i (T k)))+
      a k*R (T k)*R (T k)/(V : ℝ)
  have he : (∑ i, a k*P i (T k)*P i (T k))-
      (∑ i, (2*(a k*P i (T k)*Q i (T k))-a k*Q i (T k)*Q i (T k))) =
      a k*∑ i, (d k i)^2 := by
    rw [← sum_sub_distrib,mul_sum]
    apply sum_congr rfl
    intro i _
    unfold d
    ring
  have ha : a k ≤ 0 := by
    change -2*(r^(k+1)/(k+1 : ℕ)) ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin V)) (fun _ => (1 : ℝ)) (d k)
  simp only [one_mul,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hc
  rw [hR]
  have hV' : 0 < (V : ℝ) := by exact_mod_cast hV
  have hq := mul_le_mul_of_nonpos_left hc ha
  apply (sub_le_iff_le_add'.mp ?_)
  rw [he]
  apply (le_div_iff₀ hV').mpr
  nlinarith only [hq]

end PiPolynomialValues
