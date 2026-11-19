module

public import OddPiPowers.PolynomialValues.Numerics.SpatialQuadrature
public import OddPiPowers.PolynomialValues.Analysis.FieldIntegral

/-! A genuine upper integral on each physical frequency cell, including
the error when the maximizing node changes in its interior. -/

@[expose] public section

namespace PiPolynomialValues

open Finset MeasureTheory Set

def variationAt (rows : List SpatialLane) (k : ℕ) := maxWithFloor 0 (fun v => |v.jump k|) rows

def referenceVariation (rows : List SpatialLane) := packEval 1 641 (variationAt rows)

theorem variationAt_nonneg (rows : List SpatialLane) (j : ℕ) : 0≤variationAt rows j := by
  cases rows with
  | nil => exact le_rfl
  | cons v vs => exact (abs_nonneg (v.jump j)).trans (le_max_left _ _)

theorem SpatialLane.field_as_mesh (v : SpatialLane) (fee x : ℝ) :
    v.realField (x-1)+fee=
      meshField (1/40000) ((v.slope : ℝ)/100000) ((-(v.slope : ℝ)-v.β)/100000+fee)
        (fun j : Fin 641 => 125*j.val) (fun j => (v.jump j.val : ℝ)/100000) x := by
  unfold realField meshField
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (v.jump j : ℝ)/100000*logPrimitive (x-((125*j : ℕ) : ℝ)*(1/40000))) 641]
  simp only [sub_add_cancel,Nat.cast_mul,Nat.cast_ofNat]
  rw [show (∑ j ∈ range 641, (v.jump j : ℝ)/100000*logPrimitive (x-125*j*(1/40000)))=
      (∑ j ∈ range 641, (v.jump j : ℝ)*logPrimitive (x-125*j/40000))/100000 by
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro j _
    rw [show 125*(j : ℝ)*(1/40000)=125*j/40000 by ring]
    ring]
  ring

theorem reference_cell_integral (rows : List SpatialLane) (hp : ∀ v∈rows, v.passes=true)
    (i : ℕ) (hi : i<80000) (fee : Fin rows.length → ℝ) (left right : List PricedSpatialLane)
    (hl : ∀ v, ∃ p∈left, p.lane=rows.get v ∧ fee v≤(p.surcharge.val i : ℝ)/(40000*100000*10^9))
    (hr : ∀ v, ∃ p∈right, p.lane=rows.get v ∧ fee v≤(p.surcharge.val (i+1) : ℝ)/(40000*100000*10^9))
    (g : C(ℝ,ℝ)) (hg : ∀ x∈Icc ((i : ℝ)/40000-1) (((i : ℝ)+1)/40000-1),
      ∃ v, g x≤(rows.get v).realField x+fee v) :
    (∫ x in ((i : ℝ)/40000-1)..(((i : ℝ)+1)/40000-1), g x)≤
       (1/40000)*(((gridEnvelope left i : ℝ)+(gridEnvelope right (i+1) : ℝ))/(2*(40000*100000*10^9))+
         ∑ j : Fin 641, (variationAt rows j.val : ℝ)/100000*cellAllowance (1/40000) (nearestCell (125*j.val) i)) := by
  let V := Fin rows.length
  let G : C(ℝ,ℝ) := g.comp ⟨fun x : ℝ => x-1,continuous_id.sub continuous_const⟩
  have hB (v : V) (j : Fin 641) : |((rows.get v).jump j.val : ℝ)/100000|≤(variationAt rows j.val : ℝ)/100000 := by
    rw [abs_div,abs_of_pos (by norm_num : 0<(100000:ℝ))]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast (maxWithFloor_ge 0 (fun w : SpatialLane => |w.jump j.val|) rows (List.get_mem rows v))
  have hL (v : V) : (rows.get v).realField ((i : ℝ)/40000-1)+fee v≤(gridEnvelope left i : ℝ)/(40000*100000*10^9) := by
    obtain ⟨p,hm,hv,hf⟩ := hl v
    have H := gridEnvelope_dominates hm (hv ▸ hp _ (List.get_mem rows v)) i hi.le
    rw [hv] at H
    linarith only [H,hf]
  have hR (v : V) : (rows.get v).realField (((i : ℝ)+1)/40000-1)+fee v≤(gridEnvelope right (i+1) : ℝ)/(40000*100000*10^9) := by
    obtain ⟨p,hm,hv,hf⟩ := hr v
    have H := gridEnvelope_dominates hm (hv ▸ hp _ (List.get_mem rows v)) (i+1) (by omega)
    rw [hv,Nat.cast_succ] at H
    linarith only [H,hf]
  have H := field_cell_integral (h := (1:ℝ)/40000) (by norm_num) i (fun j : Fin 641 => 125*j.val)
    (fun (v : V) j => ((rows.get v).jump j.val : ℝ)/100000) _ hB (fun v => ((rows.get v).slope : ℝ)/100000)
    (fun v => (-((rows.get v).slope : ℝ)-(rows.get v).β)/100000+fee v) _ _
    (fun v => by rw [← (rows.get v).field_as_mesh]; simpa only [div_eq_mul_inv,one_mul] using hL v)
    (fun v => by rw [← (rows.get v).field_as_mesh]; simpa only [div_eq_mul_inv,one_mul] using hR v) G
    (fun x hx => by
      obtain ⟨v,H⟩ := hg (x-1) (by
        simp only [Set.mem_Icc] at hx ⊢
        constructor <;> linarith only [hx.1,hx.2])
      exact ⟨v,H.trans_eq ((rows.get v).field_as_mesh (fee v) x)⟩)
  dsimp only [G,ContinuousMap.comp_apply,ContinuousMap.coe_mk] at H
  rw [intervalIntegral.integral_comp_sub_right] at H
  convert H using 1 <;> ring_nf

end PiPolynomialValues
