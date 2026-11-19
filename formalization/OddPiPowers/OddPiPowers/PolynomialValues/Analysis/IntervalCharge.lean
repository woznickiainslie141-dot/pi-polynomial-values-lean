module

public import OddPiPowers.PolynomialValues.Analysis.RadialPotential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! An interval of a signed step density as a bounded linear
functional on continuous tests, including reversed or empty intervals. -/

@[expose] public section

namespace PiPolynomialValues

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

noncomputable def intervalCharge (p : C(ℝ,X)) (a b : ℝ) : ContinuousCharge X :=
  LinearMap.mkContinuous
    ({ toFun := fun f => ∫ t in a..b, f (p t)
       map_add' := fun f g => intervalIntegral.integral_add
         ((f.continuous.comp p.continuous).intervalIntegrable _ _)
         ((g.continuous.comp p.continuous).intervalIntegrable _ _)
       map_smul' := fun c f => intervalIntegral.integral_const_mul c (fun t => f (p t)) } :
      C(X,ℝ) →ₗ[ℝ] ℝ)
    |b-a| (fun f => (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t _ => f.norm_coe_le_norm (p t))).trans_eq (mul_comm _ _))

@[simp] theorem intervalCharge_apply (p : C(ℝ,X)) (a b : ℝ) (f : C(X,ℝ)) :
    intervalCharge p a b f = ∫ t in a..b, f (p t) := rfl

theorem radialPotential_interval (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (p : C(ℝ,X)) (a b : ℝ) (x : X) :
    radialPotential u r (intervalCharge p a b) x =
      ∫ t in a..b, Real.log (radialPair r (u (p t)) (u x)) := by
  rw [radialPotential_apply u hu hr hr1,intervalCharge_apply]
  simp only [radialPotential_point u hu hr hr1]

end PiPolynomialValues
