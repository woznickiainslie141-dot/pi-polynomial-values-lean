module

public import OddPiPowers.PolynomialValues.Analysis.SelectedAllocations

/-! At zero prescribed slope the same reference bounds the radial
self-interactions of every column allocation on either face. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Finset Real

theorem signed_zero_member {K : ℕ} {v : ℤ} (h : v∈signedSlopes (List.replicate K 0)) : v=0 := by
  rcases List.mem_append.mp h with h|h
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    have hr := List.mem_of_mem_tail (List.mem_reverse.mp ha)
    have ha' : a=0 := (List.mem_replicate.mp hr).2
    simp [ha']
  · exact (List.mem_replicate.mp h).2

namespace SelectedSequence

variable {P : EvaluationPlan} (W : SelectedSequence P)

theorem columns_value {i : ℕ} (hN : 0<W.mass i) (face : Bool) (c : Fin (W.size i)) :
    (faceFrequency face ((W.witness i).colIndex c).2.val : ℝ)=W.mass i*(W.columns i face c : ℝ) := by
  have h : 0<P.shape.massUnit*W.index i := Nat.cast_pos.mp
    (show (0 : ℝ)<((P.shape.massUnit*W.index i : ℕ) : ℝ) from hN)
  let a : Column (P.shape.band (W.index i)) := (W.witness i).colIndex c
  have hh : (W.columns i face c : ℝ)=(faceFrequency face a.2.val : ℝ)*(W.mass i)⁻¹ :=
    (bandFrequency_value P.shape P.width h (columnReflection _ face a)).trans
      (congrArg (fun v : ℤ => (v : ℝ)*(W.mass i)⁻¹) (columnReflection_frequency _ face a))
  rw [hh]
  change (faceFrequency face a.2.val : ℝ)=W.mass i*((faceFrequency face a.2.val : ℝ)*(W.mass i)⁻¹)
  field_simp [hN.ne'] <;> ring

theorem zero_reference_bound (k i : ℕ) (hN : 0<W.mass i)
    (E : ReferenceEvidence P.shape P.anchor (List.replicate P.shape.ratios.length 0) 0 P.rates.ordinary)
    (face : Bool) (d : W.placement i) :
    (∑ u, radialSelf (innerRadius k) (W.charge i face d u)/2)≤W.finiteReference E k i := by
  have hN' : 0<P.shape.massUnit*(4*W.grid i) := Nat.cast_pos.mp
    (show (0 : ℝ)<((P.shape.massUnit*(4*W.grid i) : ℕ) : ℝ) from hN)
  have H := selected_reference_bound E P.order P.width hN' (W.witness i).count d (W.witness i).colIndex face
    (le_refl _) (fun _ => rfl) (fun _ => 0) (fun _ => Nat.zero_le _) (fun _ _ h => (h rfl).elim)
    (innerRadius_bounds k).1.le (innerRadius_bounds k).2
  have hs (u : Fin E.rows.length) : (E.rows.get u).slope=0 := by
    apply signed_zero_member
    rw [← E.field]
    exact List.mem_map.mpr ⟨E.rows.get u,List.get_mem _ _,rfl⟩
  have hz : linearFrequency 0=0 := by ext x; simp [linearFrequency]
  change (∑ u, ((W.charge i face d u) (linearFrequency (((E.rows.get (E.rowRank P.order u)).slope : ℝ)/100000))+
    radialSelf (innerRadius k) (W.charge i face d u)/2))+_≤W.finiteReference E k i at H
  simpa only [hs,Int.cast_zero,zero_div,hz,map_zero,zero_add,ite_true,sum_const_zero,mul_zero,add_zero] using H

end SelectedSequence
end PiPolynomialValues
