module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceCell
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Data.List.Enum

/-! The cell test is the true continuous maximum of the affine fields
and logarithmic potentials, with the assigned center held fixed from
the left endpoint to the right endpoint. -/

@[expose] public section

namespace PiPolynomialValues

open Finset MeasureTheory Set

theorem SpatialLane.realField_continuous (v : SpatialLane) : Continuous v.realField := by
  unfold realField
  apply Continuous.div_const
  apply Continuous.add (by fun_prop)
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul (logPrimitive_continuous.comp (by fun_prop))

noncomputable def cellField (rows : List SpatialLane) (hn : 0<rows.length) (fee : Fin rows.length → ℝ) : C(ℝ,ℝ) :=
  univ.sup' ⟨⟨0,hn⟩,mem_univ _⟩ (fun v => ⟨fun x => (rows.get v).realField x+fee v,
    (rows.get v).realField_continuous.add continuous_const⟩)

theorem cellField_eval (rows : List SpatialLane) (hn : 0<rows.length) (fee : Fin rows.length → ℝ) (x : ℝ) :
    cellField rows hn fee x=univ.sup' ⟨⟨0,hn⟩,mem_univ _⟩
      (fun v : Fin rows.length => (rows.get v).realField x+fee v) :=
  ContinuousMap.sup'_apply (s := univ) ⟨⟨0,hn⟩,mem_univ _⟩
    (fun v : Fin rows.length => (⟨fun t => (rows.get v).realField t+fee v,
      (rows.get v).realField_continuous.add continuous_const⟩ : C(ℝ,ℝ))) x

theorem cellField_upper (rows : List SpatialLane) (hn : 0<rows.length) (fee : Fin rows.length → ℝ)
    (v : Fin rows.length) (x : ℝ) : (rows.get v).realField x+fee v≤cellField rows hn fee x := by
  rw [cellField_eval]
  exact le_sup' (f := fun i : Fin rows.length => (rows.get i).realField x+fee i) (mem_univ v)

theorem cellField_attains (rows : List SpatialLane) (hn : 0<rows.length) (fee : Fin rows.length → ℝ) (x : ℝ) :
    ∃ v, cellField rows hn fee x≤(rows.get v).realField x+fee v := by
  rw [cellField_eval]
  obtain ⟨v,_,h⟩ := exists_mem_eq_sup' (s := (univ : Finset (Fin rows.length))) ⟨⟨0,hn⟩,mem_univ _⟩
    (fun j => (rows.get j).realField x+fee j)
  exact ⟨v,h.le⟩

noncomputable def cellFee (a : AnchorPlan) (price : ℤ) (i j : ℕ) : ℝ :=
  if a.center i=j then 0 else (price : ℝ)/10^7

theorem bare_endpoint (rows : List SpatialLane) (v : Fin rows.length) (i : ℕ) :
    ∃ p∈bareLanes rows, p.lane=rows.get v ∧ (0 : ℝ)≤(p.surcharge.val i : ℝ)/(40000*100000*10^9) := by
  refine ⟨⟨rows.get v,[]⟩,List.mem_map.mpr ⟨_,List.get_mem _ _,rfl⟩,rfl,?_⟩
  norm_num [GridWeights.val]

theorem fee_endpoint (rows : List SpatialLane) (a : AnchorPlan) (hc : a.covers 0 80000=true)
    {price : ℤ} (hp : 0≤price) (i : ℕ) (hi : i<80000) (d : ℕ) (v : Fin rows.length) :
    ∃ p∈feeLanes rows a d price, p.lane=rows.get v ∧
      cellFee a price i v.val≤(p.surcharge.val (i+d) : ℝ)/(40000*100000*10^9) := by
  let fee := price*400000000000
  have hf : 0≤fee := by dsimp [fee]; positivity
  have hm : (rows.get v,v.val)∈rows.zipIdx := by
    obtain ⟨q,hq,he⟩ := List.exists_mem_zipIdx' (l := rows) (p := fun p => p=(rows.get v,v.val)) |>.mpr
      ⟨v.val,v.isLt,rfl⟩
    exact he ▸ hq
  refine ⟨⟨rows.get v,a.charges v.val d fee⟩,List.mem_map.mpr ⟨_,hm,rfl⟩,rfl,?_⟩
  have H := a.charge_lower hc (Nat.zero_le i) hi v.val d hf
  change cellFee a price i v.val≤((a.charges v.val d fee).val (i+d) : ℝ)/(40000*100000*10^9)
  by_cases h : a.center i=v.val
  · simp only [h,if_true,cellFee] at H ⊢
    exact div_nonneg (by exact_mod_cast H) (by norm_num)
  · simp only [h,if_false,cellFee] at H ⊢
    have hh : (price : ℝ)*400000000000≤((a.charges v.val d fee).val (i+d) : ℝ) := by exact_mod_cast H
    linarith only [hh]

noncomputable def gridCellIntegral (g : C(ℝ,ℝ)) (i : ℕ) :=
  ∫ x in ((i : ℝ)/40000-1)..(((i : ℝ)+1)/40000-1), g x

noncomputable def gridCellError (rows : List SpatialLane) (i : ℕ) :=
  ∑ j : Fin 641, (variationAt rows j.val : ℝ)/100000*cellAllowance (1/40000) (nearestCell (125*j.val) i)

theorem unpaid_cell_bound (rows : List SpatialLane) (hn : 0<rows.length) (hv : ∀ v∈rows, v.passes=true)
    (i : ℕ) (hi : i<80000) :
    gridCellIntegral (cellField rows hn (fun _ => 0)) i≤(1/40000)*(
      ((gridEnvelope (bareLanes rows) i : ℝ)+gridEnvelope (bareLanes rows) (i+1))/(2*(40000*100000*10^9))+gridCellError rows i) :=
  reference_cell_integral rows hv i hi _ _ _ (fun v => bare_endpoint rows v i) (fun v => bare_endpoint rows v (i+1))
    _ (fun x _ => cellField_attains rows hn _ x)

theorem paid_cell_bound (rows : List SpatialLane) (hn : 0<rows.length) (hv : ∀ v∈rows, v.passes=true)
    (a : AnchorPlan) (hc : a.covers 0 80000=true) {price : ℤ} (hp : 0≤price) (i : ℕ) (hi : i<80000) :
    gridCellIntegral (cellField rows hn (fun v => cellFee a price i v.val)) i≤(1/40000)*(
      ((gridEnvelope (feeLanes rows a 0 price) i : ℝ)+gridEnvelope (feeLanes rows a 1 price) (i+1))/
      (2*(40000*100000*10^9))+gridCellError rows i) :=
  reference_cell_integral rows hv i hi _ _ _ (fun v => fee_endpoint rows a hc hp i hi 0 v)
    (fun v => fee_endpoint rows a hc hp i hi 1 v) _ (fun x _ => cellField_attains rows hn _ x)

end PiPolynomialValues
