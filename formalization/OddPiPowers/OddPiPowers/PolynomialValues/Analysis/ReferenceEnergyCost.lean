module

public import OddPiPowers.PolynomialValues.Analysis.ResidualCharge
public import OddPiPowers.PolynomialValues.Analysis.RadialDuality

/-! The self-energies in the dual bound are the stated signed integer
costs. The residual can also use negative semidefiniteness. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Filter
open scoped Topology

noncomputable def innerRadius (k : ℕ) : ℝ := 1-((k : ℝ)+2)⁻¹

theorem innerRadius_bounds (k : ℕ) : 0 < innerRadius k ∧ innerRadius k < 1 := by
  have h : 1 < (k : ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  exact ⟨sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr h),sub_lt_self _ (by positivity)⟩

theorem innerRadius_tendsto : Tendsto innerRadius atTop (𝓝 1) := by
  have H := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  change Tendsto (fun k : ℕ => 1-((k : ℝ)+2)⁻¹) atTop (𝓝 1)
  simpa only [Function.comp_def,sub_zero] using H.const_sub 1

theorem mesh_self_nonpos {n step : ℕ} (h : (n-1)*step≤80000) (d : ℕ → ℤ) :
    meshReference h d (meshLimitPotential h d)≤0 := by
  have H := (meshReference h d).continuous.continuousAt.tendsto.comp (meshReference_radial_limit h d
    (fun k => (innerRadius_bounds k).1) (fun k => (innerRadius_bounds k).2) innerRadius_tendsto)
  exact le_of_tendsto H (Eventually.of_forall (fun k => radialInteraction_nonpos unitFrequency unitFrequency_norm
    (innerRadius_bounds k).1.le (innerRadius_bounds k).2 (meshReference h d)))

noncomputable def laneCharge (v : SpatialLane) := meshReference (n := 641) (step := 125) (by decide) v.jump
noncomputable def lanePotential (v : SpatialLane) := meshLimitPotential (n := 641) (step := 125) (by decide) v.jump
noncomputable def residualPotential (rows : List SpatialLane) (s : FourPeriod.Shape) :=
  meshLimitPotential (n := 80001) (step := 1) (by decide) (residualJump rows s.widths)

theorem regular_self_cost (E : EnergySection 641 125 0 641) (v : SpatialLane) (h : v.passes=true) :
    -(laneCharge v (lanePotential v))/2≤(regularEnergy E v : ℝ)/(2*10^12*100000^2) := by
  rw [laneCharge,lanePotential,meshReference_self _ _ (v.sound h).2.1]
  linarith only [regularEnergy_upper E v h]

private theorem scale_residual_self {x e : ℝ} {z : ℤ} (hx : x≤0) (he : x= -e/100000^2)
    (hb : -(10^12*e)≤(z : ℝ)) : x≤(min 0 z : ℤ)/(10^12*100000^2 : ℝ) := by
  rw [Int.cast_min,Int.cast_zero,← min_div_div_right (by norm_num : (0 : ℝ)≤10^12*100000^2),zero_div]
  exact le_min hx (by linarith only [he,hb])

attribute [local irreducible] meshReference meshLimitPotential meshPairEnergy residualEnergy

private theorem residual_charge_eq (s : FourPeriod.Shape) (rows : List SpatialLane) (hw : ∀ w∈s.widths, w≤10000) :
    FourPeriod.fullBandCharge s-∑ j : Fin rows.length, laneCharge (rows.get j)=
      meshReference (n := 80001) (step := 1) (by decide) (residualJump rows s.widths) :=
  (residual_meshReference s rows hw).symm

private theorem finite_self_le {n step : ℕ} (h : (n-1)*step≤80000) (d : ℕ → ℤ)
    (hz : ∑ i ∈ range n, d i=0) (z : ℤ) (hb : -(10^12*meshPairEnergy n step d)≤(z : ℝ)) :
    meshReference h d (meshLimitPotential h d)≤(min 0 z : ℤ)/(10^12*100000^2 : ℝ) :=
  scale_residual_self (x := meshReference h d (meshLimitPotential h d)) (e := meshPairEnergy n step d) (z := z)
    (mesh_self_nonpos h d) (meshReference_self h d hz) hb

private theorem fine_grid_value (d : ℕ → ℤ) (hz : ∑ i ∈ range 80001, d i=0)
    (e : ℤ) (hb : -(10^12*meshPairEnergy 80001 1 d)≤(e : ℝ)) :
    meshReference (n := 80001) (step := 1) (by decide) d
      (meshLimitPotential (n := 80001) (step := 1) (by decide) d)≤(min 0 e : ℤ)/(10^12*100000^2 : ℝ) :=
  @finite_self_le 80001 1 (by decide) d hz e hb

private theorem transfer_charge_bound (P Q : ContinuousCharge FrequencyInterval) (f g : C(FrequencyInterval,ℝ))
    (u : ℝ) (he : P=Q) (hf : f=g) (h : Q g≤u) : P f≤u := by rw [he,hf]; exact h

theorem residual_self_cost (E : EnergySection 80001 1 0 80001) (s : FourPeriod.Shape)
    (rows : List SpatialLane) (hd : ∀ v∈rows, v.passes=true) (hw : ∀ w∈s.widths, w≤10000)
    (hn : 200000*(s.widths.length : ℤ)+jumpBudget rows≤10^13) :
    (FourPeriod.fullBandCharge s-∑ j : Fin rows.length, laneCharge (rows.get j)) (residualPotential rows s) ≤
      (min 0 (residualEnergy E rows s.widths) : ℤ)/(10^12*100000^2 : ℝ) :=
  transfer_charge_bound (FourPeriod.fullBandCharge s-∑ j : Fin rows.length, laneCharge (rows.get j))
    (meshReference (n := 80001) (step := 1) (by decide) (residualJump rows s.widths)) (residualPotential rows s)
    (meshLimitPotential (n := 80001) (step := 1) (by decide) (residualJump rows s.widths))
    ((min 0 (residualEnergy E rows s.widths) : ℤ)/(10^12*100000^2 : ℝ)) (residual_charge_eq s rows hw) rfl
    (fine_grid_value (residualJump rows s.widths) (residualJump_zero rows s.widths hw hd)
      (residualEnergy E rows s.widths) (residualEnergy_upper E rows s.widths hd hw hn))

end PiPolynomialValues
