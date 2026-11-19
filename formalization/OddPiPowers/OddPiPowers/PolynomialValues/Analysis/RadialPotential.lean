module

public import OddPiPowers.PolynomialValues.Analysis.RadialFourier
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.Banach

/-! The radial potential of any signed continuous linear functional.
Both an atomic allocation and a step density act on the same space. -/

@[expose] public section

namespace PiPolynomialValues

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

abbrev ContinuousCharge (X : Type*) [TopologicalSpace X] := C(X,ℝ) →L[ℝ] ℝ

noncomputable def unitMoment (u : C(X,ℂ)) (k : ℕ) : C(X,ℝ) :=
  ⟨fun x => (u x^(k+1)).re,Complex.continuous_re.comp (u.continuous.pow _)⟩

theorem norm_unitMoment_le (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1) (k : ℕ) :
    ‖unitMoment u k‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro x
  change |(u x^(k+1)).re| ≤ 1
  exact (Complex.abs_re_le_norm _).trans_eq (by rw [norm_pow,hu,one_pow])

noncomputable def radialPotential (u : C(X,ℂ)) (r : ℝ) (L : ContinuousCharge X) : C(X,ℝ) :=
  ∑' k : ℕ, (-2*radialFourierWeight r k*L (unitMoment u k)) • unitMoment u k

theorem radialPotential_hasSum (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (L : ContinuousCharge X) :
    HasSum (fun k : ℕ => (-2*radialFourierWeight r k*L (unitMoment u k)) • unitMoment u k)
      (radialPotential u r L) := by
  apply Summable.hasSum
  apply ((summable_geometric_of_lt_one hr hr1).mul_left (2*‖L‖)).of_norm_bounded
  intro k
  have hU := norm_unitMoment_le u hu k
  have hL : ‖L (unitMoment u k)‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left hU (norm_nonneg L))
  have hW : 0 ≤ radialFourierWeight r k := by unfold radialFourierWeight; positivity
  have hw : radialFourierWeight r k ≤ r^k := by
    unfold radialFourierWeight
    apply (div_le_iff₀ (by positivity)).mpr
    rw [pow_succ]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr k)
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [norm_smul,norm_mul,norm_mul,Real.norm_of_nonneg hW]
  norm_num
  calc
    _ ≤ (2*r^k*‖L‖)*1 := by gcongr; exact hL
    _ = _ := by ring

noncomputable def radialInteraction (u : C(X,ℂ)) (r : ℝ) (P Q : ContinuousCharge X) : ℝ :=
  P (radialPotential u r Q)

theorem radialInteraction_hasSum (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (P Q : ContinuousCharge X) :
    HasSum (fun k : ℕ => -2*radialFourierWeight r k*P (unitMoment u k)*Q (unitMoment u k))
      (radialInteraction u r P Q) := by
  have h := P.hasSum (radialPotential_hasSum u hu hr hr1 Q)
  refine h.congr_fun fun k => ?_
  rw [map_smul,smul_eq_mul]
  ring

theorem radialInteraction_comm (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (P Q : ContinuousCharge X) :
    radialInteraction u r P Q = radialInteraction u r Q P := by
  apply (radialInteraction_hasSum u hu hr hr1 P Q).unique
  exact (radialInteraction_hasSum u hu hr hr1 Q P).congr_fun (fun k => by ring)

theorem radialPotential_point (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (x y : X) :
    radialPotential u r (ContinuousMap.evalCLM ℝ x) y = Real.log (radialPair r (u y) (u x)) :=
  (radialInteraction_hasSum u hu hr hr1 (ContinuousMap.evalCLM ℝ y) (ContinuousMap.evalCLM ℝ x)).unique
    (log_radial_pair_hasSum hr hr1 (hu y) (hu x))

theorem radialPotential_apply (u : C(X,ℂ)) (hu : ∀ x, ‖u x‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (L : ContinuousCharge X) (x : X) :
    radialPotential u r L x = L (radialPotential u r (ContinuousMap.evalCLM ℝ x)) :=
  radialInteraction_comm u hu hr hr1 (ContinuousMap.evalCLM ℝ x) L

end PiPolynomialValues
