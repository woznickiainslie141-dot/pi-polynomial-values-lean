module

public import OddPiPowers.PolynomialValues.Analysis.RadialPotential

/-! A finite allocation acts by its actual evaluations on continuous
potentials and its radial energy is exactly the full ordered pair sum. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def atomicCharge (x : ι → X) (w : ι → ℝ) : ContinuousCharge X :=
  ∑ i, w i • ContinuousMap.evalCLM ℝ (x i)

theorem atomicCharge_apply (x : ι → X) (w : ι → ℝ) (f : C(X,ℝ)) :
    atomicCharge x w f = ∑ i, w i*f (x i) := by
  simp [atomicCharge,ContinuousLinearMap.sum_apply,smul_eq_mul]

theorem atomicInteraction_eq (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) (x : ι → X) (y : κ → X) (w : ι → ℝ) (b : κ → ℝ) :
    radialInteraction u r (atomicCharge x w) (atomicCharge y b) =
      ∑ i, ∑ j, w i*b j*Real.log (radialPair r (u (y j)) (u (x i))) := by
  rw [radialInteraction,atomicCharge_apply]
  apply sum_congr rfl
  intro i _
  rw [radialPotential_apply u hu hr hr1,atomicCharge_apply,mul_sum]
  apply sum_congr rfl
  intro j _
  rw [radialPotential_point u hu hr hr1,mul_assoc]

end PiPolynomialValues
