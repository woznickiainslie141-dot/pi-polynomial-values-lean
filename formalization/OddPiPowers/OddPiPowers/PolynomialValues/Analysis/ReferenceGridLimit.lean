module

public import OddPiPowers.PolynomialValues.Analysis.ShapeGridCells
public import OddPiPowers.PolynomialValues.Analysis.PhysicalQuantiles
public import OddPiPowers.PolynomialValues.Numerics.ReferenceIntegral

/-! The sum of the column prices on the actual mesh converges to the same
integral enclosed by the complete integer trapezoid certificate. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter
open scoped Topology

noncomputable def layerCellField (rows : List SpatialLane) (hr : 0 < rows.length) (a : AnchorPlan)
    (p : ℤ) (j i : ℕ) : C(ℝ,ℝ) :=
  if p=0 ∨ j=0 then cellField rows hr (fun _ => 0) else cellField rows hr (fun v => cellFee a p i v.val)

theorem sum_layer_hit (ws : List ℕ) (i : ℕ) :
    (∑ j : Fin ws.length, ((bandSpan (ws.get j)).hit i : ℝ))=(bandCount ws i : ℝ) := by
  let f (w : ℕ) := ((bandSpan w).hit i : ℝ)
  have H := sum_get_real ws f
  simpa only [bandCount,Int.cast_list_sum,List.map_map,Function.comp_def,f] using H

theorem layerCell_sum (rows : List SpatialLane) (hr : 0 < rows.length) (ws : List ℕ)
    (a : AnchorPlan) (p : ℤ) (i : ℕ) :
    (∑ j : Fin ws.length, ((bandSpan (ws.get j)).hit i : ℝ)*
      gridCellIntegral (layerCellField rows hr a p j.val i) i)=cellValue rows hr ws a p i := by
  by_cases hp : p=0
  · simp only [layerCellField,cellValue,hp,true_or,if_true,← sum_mul,sum_layer_hit]
  cases ws with
  | nil => simp [cellValue,bandCount,hp]
  | cons w ws =>
    change (∑ j : Fin (ws.length+1), ((bandSpan ((w::ws).get j)).hit i : ℝ)*
      gridCellIntegral (layerCellField rows hr a p j.val i) i)=_
    rw [Fin.sum_univ_succ (n := ws.length)]
    simp only [Fin.val_zero,Fin.val_succ,Nat.succ_ne_zero,layerCellField,or_true,or_false,if_true,if_neg hp,
      List.get_cons_zero,List.get_cons_succ,← sum_mul,sum_layer_hit]
    have hs := sum_layer_hit ws i
    change (∑ j : Fin ws.length, ((bandSpan ws[j.val]).hit i : ℝ))=_ at hs
    simp only [cellValue,hp,if_false,List.take_succ_cons,List.take_zero,List.tail_cons,bandCount,List.map_nil,
      List.sum_nil,List.map_cons,List.sum_cons,add_zero,Int.cast_list_sum,List.map_map,Function.comp_def] at hs ⊢
    exact congrArg (fun x : ℝ => ((bandSpan w).hit i : ℝ)*gridCellIntegral (cellField rows hr (fun _ => 0)) i+
      x*gridCellIntegral (cellField rows hr (fun v => cellFee a p i v.val)) i) hs

noncomputable def columnPriceSum (s : Shape) (rows : List SpatialLane) (hr : 0 < rows.length) (a : AnchorPlan)
    (p : ℤ) (t : ℕ) : ℝ :=
  let N := s.massUnit*(4*t)
  (N : ℝ)⁻¹*∑ c : Column (s.band (4*t)), layerCellField rows hr a p c.1.val
    (physicalCell (s.rows.sum*t) c.2.val) ((c.2.val : ℝ)*(N : ℝ)⁻¹)

theorem columnPriceSum_limit (s : Shape) (hs : 0 < s.rows.sum) (hw : ∀ w∈s.widths, w≤10000)
    (rows : List SpatialLane) (hr : 0 < rows.length) (a : AnchorPlan) (p : ℤ) :
    Tendsto (columnPriceSum s rows hr a p) atTop (𝓝 (∑ i ∈ range 80000, cellValue rows hr s.widths a p i)) := by
  have H := physical_shape_limit s hs hw (fun j => layerCellField rows hr a p j.val)
  rw [sum_comm] at H
  simp only [layerCell_sum] at H
  exact H

theorem columnPriceSum_envelope (rows : List SpatialLane) (hr : 0 < rows.length) (a : AnchorPlan)
    {p : ℤ} (hp : 0≤p) (j i : ℕ) (z : ℝ) (v : Fin rows.length) :
    (rows.get v).realField z+(if j≠0 ∧ a.center i≠v.val then (p : ℝ)/10^7 else 0)≤
      layerCellField rows hr a p j i z := by
  by_cases h : p=0 ∨ j=0
  · rw [layerCellField,if_pos h]
    have he : (if j≠0 ∧ a.center i≠v.val then (p : ℝ)/10^7 else 0)=0 := by
      rcases h with h|h <;> simp [h]
    rw [he]
    exact cellField_upper rows hr (fun _ => 0) v z
  · have hj : j≠0 := fun he => h (Or.inr he)
    rw [layerCellField,if_neg h]
    have he : (if j≠0 ∧ a.center i≠v.val then (p : ℝ)/10^7 else 0)=cellFee a p i v.val := by
      by_cases he : a.center i=v.val <;> simp [cellFee,hj,he]
    rw [he]
    exact cellField_upper rows hr (fun k => cellFee a p i k.val) v z

end PiPolynomialValues.FourPeriod
