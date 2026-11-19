module

public import OddPiPowers.PolynomialValues.Analysis.RegularizedInterval
public import OddPiPowers.PolynomialValues.Analysis.RadialDuality

/-! The signed interval data in the spatial certificate define genuine
charges, with exact limiting potentials and exact quadratic interactions. -/

@[expose] public section

namespace PiPolynomialValues

open Finset MeasureTheory Filter
open scoped Topology Interval

structure SpatialInterval where
  left : ℝ
  right : ℝ
  left_mem : -1 ≤ left
  ordered : left ≤ right
  right_mem : right ≤ 1

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def stepCharge (A : ι → SpatialInterval) (w : ι → ℝ) : ContinuousCharge FrequencyInterval :=
  ∑ i, w i • intervalCharge frequencyProjection (A i).left (A i).right

noncomputable def stepPotential (A : ι → SpatialInterval) (w : ι → ℝ) : C(FrequencyInterval,ℝ) :=
  ∑ i, w i • intervalPotential (A i).left (A i).right

noncomputable def intervalInteraction (A B : SpatialInterval) :=
  energyPrimitive (B.right-A.left)-energyPrimitive (B.right-A.right)-
  energyPrimitive (B.left-A.left)+energyPrimitive (B.left-A.right)

theorem step_radial_potential (A : ι → SpatialInterval) (w : ι → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) :
    radialPotential unitFrequency r (stepCharge A w) = ∑ i, w i •
      radialPotential unitFrequency r (intervalCharge frequencyProjection (A i).left (A i).right) := by
  ext x
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,radialPotential_apply _ unitFrequency_norm hr hr1,
    stepCharge,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]

theorem stepPotential_limit {η : Type*} {F : Filter η} {r : η → ℝ} (hr : ∀ i, 0 < r i)
    (hr1 : ∀ i, r i < 1) (ht : Tendsto r F (𝓝 1)) (A : ι → SpatialInterval) (w : ι → ℝ) :
    Tendsto (fun i => radialPotential unitFrequency (r i) (stepCharge A w)) F
      (𝓝 (stepPotential A w)) := by
  have h (j : ι) := (intervalPotential_limit hr hr1 ht (A j).left_mem (A j).ordered (A j).right_mem).const_smul (w j)
  simp_rw [fun i => step_radial_potential A w (hr i).le (hr1 i)]
  exact tendsto_finsetSum _ (fun j _ => h j)

theorem intervalCharge_potential (A B : SpatialInterval) :
    intervalCharge frequencyProjection A.left A.right (intervalPotential B.left B.right) =
      intervalInteraction A B := by
  rw [intervalCharge_apply]
  have he : (∫ t in A.left..A.right, intervalPotential B.left B.right (frequencyProjection t)) =
      ∫ t in A.left..A.right, (logPrimitive (B.right-t)-logPrimitive (B.left-t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le A.ordered] at ht
    change logPrimitive (B.right-(frequencyProjection t : ℝ))-logPrimitive (B.left-(frequencyProjection t : ℝ)) = _
    rw [projected_frequency A.left_mem A.right_mem ht]
  have hI (z : ℝ) : IntervalIntegrable (fun t : ℝ => logPrimitive (z-t)) volume A.left A.right :=
    (logPrimitive_continuous.comp (by fun_prop : Continuous fun t : ℝ => z-t)).intervalIntegrable _ _
  rw [he,intervalIntegral.integral_sub (hI _) (hI _),intervalIntegral.integral_comp_sub_left,
    intervalIntegral.integral_comp_sub_left,integral_logPrimitive,integral_logPrimitive,intervalInteraction]
  ring

theorem stepCharge_potential (A : ι → SpatialInterval) (B : κ → SpatialInterval) (w : ι → ℝ) (v : κ → ℝ) :
    stepCharge A w (stepPotential B v) = ∑ i, ∑ j, w i*v j*intervalInteraction (A i) (B j) := by
  simp only [stepCharge,stepPotential,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    map_sum,map_smul,smul_eq_mul,intervalCharge_potential,mul_sum,mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem stepInteraction_limit {η : Type*} {F : Filter η} {r : η → ℝ} (hr : ∀ i, 0 < r i)
    (hr1 : ∀ i, r i < 1) (ht : Tendsto r F (𝓝 1)) (A : ι → SpatialInterval)
    (B : κ → SpatialInterval) (w : ι → ℝ) (v : κ → ℝ) :
    Tendsto (fun i => radialInteraction unitFrequency (r i) (stepCharge A w) (stepCharge B v)) F
      (𝓝 (∑ i, ∑ j, w i*v j*intervalInteraction (A i) (B j))) := by
  rw [← stepCharge_potential]
  exact ((stepCharge A w).continuous.tendsto _).comp (stepPotential_limit hr hr1 ht B v)

end PiPolynomialValues
