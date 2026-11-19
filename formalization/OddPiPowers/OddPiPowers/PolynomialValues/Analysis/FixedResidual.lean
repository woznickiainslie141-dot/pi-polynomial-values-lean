module

public import OddPiPowers.PolynomialValues.Analysis.RadialDuality
import Mathlib.Tactic.Linarith

/-! Replace the varying residual self-interaction by a fixed signed
reference and a single continuous test of the total empirical measure. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem radial_residual_tangent (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖=1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) (R S : ContinuousCharge X) :
    radialInteraction u r R R ≤
      2*(R-S) (radialPotential u r S)+radialInteraction u r S S := by
  let E := radialInteraction u r
  have hleft (P Q T : ContinuousCharge X) : E (P-Q) T=E P T-E Q T := rfl
  have hright (P Q T : ContinuousCharge X) : E P (Q-T)=E P Q-E P T := by
    calc
      E P (Q-T) = E (Q-T) P := radialInteraction_comm u hu hr hr1 _ _
      _ = E Q P-E T P := hleft _ _ _
      _ = E P Q-E P T := congrArg₂ (·-·) (radialInteraction_comm u hu hr hr1 Q P)
        (radialInteraction_comm u hu hr hr1 T P)
  have h := radialInteraction_nonpos u hu hr hr1 (R-S)
  change E (R-S) (R-S) ≤ 0 at h
  rw [hleft,hright,hright,show E S R=E R S from radialInteraction_comm u hu hr hr1 S R] at h
  change E R R ≤ 2*(E R S-E S S)+E S S
  linarith

theorem radial_dual_fixed {V : ℕ} (hV : 0<V) (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖=1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) (P Q : Fin V → ContinuousCharge X) (ν : ContinuousCharge X) :
    let S := ν-∑ i, Q i
    (∑ i, radialInteraction u r (P i) (P i)) ≤
      (∑ i, (2*P i (radialPotential u r (Q i))-radialInteraction u r (Q i) (Q i)))+
        (2*((∑ i, P i)-ν) (radialPotential u r S)+radialInteraction u r S S)/V := by
  intro S
  let R : ContinuousCharge X := ∑ i, (P i-Q i)
  have he : R-S=(∑ i, P i)-ν := by dsimp only [R,S]; rw [sum_sub_distrib]; abel
  have ht := radial_residual_tangent u hu hr hr1 R S
  rw [he] at ht
  exact (radial_dual_residual hV u hu hr hr1 P Q).trans
    (add_le_add_right (div_le_div_of_nonneg_right ht (Nat.cast_nonneg V)) _)

end PiPolynomialValues
