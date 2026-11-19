module

public import OddPiPowers.PolynomialValues.Analysis.UniformReferences

/-! Convert a reference-field bound for a maximizing permutation into one
inequality for the boundary slope and the mass of paid column labels. -/

@[expose] public section

namespace PiPolynomialValues.SelectedSequence

open FourPeriod Finset Real

variable {P : EvaluationPlan} (W : SelectedSequence P)

noncomputable def columns (i : ℕ) (face : Bool) (c : Fin (W.size i)) :=
  bandFrequency P.shape (W.index i) (columnReflection _ face ((W.witness i).colIndex c))

abbrev placement (i : ℕ) := ((u : Fin P.groups.flatten.length) × Fin ((W.witness i).count u)) ≃ Fin (W.size i)

noncomputable def charge (i : ℕ) (face : Bool) (d : W.placement i) :=
  allocationCharge (W.witness i).count d (W.columns i face) (W.mass i)

def markedOffCenter (i : ℕ) (d : W.placement i) (mark : Fin (W.size i) → ℕ) : Prop :=
  ∀ u j, mark (d ⟨u,j⟩)≠0 → scannedNode P.groups u≠
    centeredGridValue P.shape P.anchor (W.grid i) ((W.witness i).colIndex (d ⟨u,j⟩)).2.val

theorem field_bound (k i : ℕ) (hN : 0<W.mass i) (t : AngleLabel) {p : ℤ} {B : ℚ}
    (E : ReferenceEvidence P.shape P.anchor t.slopes p B) (face : Bool) (hp : 0≤p) (hface : face=true → p=0)
    (d : W.placement i) (mark : Fin (W.size i) → ℕ) (hm : ∀ c, mark c≤((W.witness i).colIndex c).1.val)
    (hoff : W.markedOffCenter i d mark) :
    (∑ u, firstMoment (W.charge i face d u)*(signedLabelSlope t (P.order.rank u).val : ℝ))+
      (∑ u, radialSelf (innerRadius k) (W.charge i face d u)/2)+
      markedMass mark (W.mass i)*((p : ℝ)/10^7)≤W.finiteReference E k i := by
  have hN' : 0<P.shape.massUnit*(4*W.grid i) := by
    exact Nat.cast_pos.mp (show (0 : ℝ)<((P.shape.massUnit*(4*W.grid i) : ℕ) : ℝ) from hN)
  have H := selected_reference_bound E P.order P.width hN' (W.witness i).count d (W.witness i).colIndex
    face hp hface mark hm hoff (innerRadius_bounds k).1.le (innerRadius_bounds k).2
  have h (u : Fin P.groups.flatten.length) := signedLabelSlope_of_evidence E (E.rowRank P.order u)
  change (∑ u, ((W.charge i face d u) (linearFrequency (((E.rows.get (E.rowRank P.order u)).slope : ℝ)/100000))+
      radialSelf (innerRadius k) (W.charge i face d u)/2))+
      (W.mass i)⁻¹*(∑ c, if mark c=0 then 0 else (p : ℝ)/10^7)≤W.finiteReference E k i at H
  simp only [← h,evaluate_linear,sum_add_distrib,scaled_mark_price] at H
  exact (le_of_eq (by congr 2; exact sum_congr rfl (fun u _ => mul_comm _ _))).trans H

theorem mixed_field_bound (k i : ℕ) (hN : 0<W.mass i) {ε : ℝ} (hr : W.referencesFit k i ε)
    (w : ℂ) (hi : w.im≠0) (hθ : P.design.weightAt (foldedAngle w) (fun _ => 1)=1)
    (d : W.placement i) (mark : Fin (W.size i) → ℕ) (hm : ∀ c, mark c≤((W.witness i).colIndex c).1.val)
    (hoff : W.markedOffCenter i d mark) :
    let face := upperSide w
    let Q := W.charge i face d
    (∑ u, firstMoment (Q u)*(∑ j : Fin P.cuts.length, (nodeSign j.val (scannedNode P.groups u) : ℝ)*
      (P.design.directionForm j.val).field (foldedAngle w)))+
      (∑ u, radialSelf (innerRadius k) (Q u)/2)+markedMass mark (W.mass i)*P.design.faceFee w≤
      (P.rates.length : ℝ)*P.design.faceEnergy w+ε := by
  intro face Q
  let f (u : Fin P.groups.flatten.length) (t : AngleLabel) := (signedLabelSlope t (P.order.rank u).val : ℝ)
  let fee (t : AngleLabel) : ℝ := if face then 0 else (t.price : ℝ)/10^7
  let cost (t : AngleLabel) : ℝ := if face then (t.ordinary : ℝ) else (t.tilted : ℝ)
  let E := ∑ u, radialSelf (innerRadius k) (Q u)/2
  let M := markedMass mark (W.mass i)
  have H (t : AngleLabel) (ht : t∈P.design.labels) :
      (∑ u, firstMoment (Q u)*f u t)+E+M*fee t≤(P.rates.length : ℝ)*cost t+ε := by
    obtain ⟨l,rfl⟩ := List.mem_iff_get.mp ht
    cases hf : face with
    | true =>
      have hh := W.field_bound k i hN _ (P.ordinaryReference l) face (le_refl _) (fun _ => rfl) d mark hm hoff
      simpa only [Q,E,M,f,cost,fee,hf,if_true,Int.cast_zero,zero_div,mul_zero,add_zero] using hh.trans (hr l).1
    | false =>
      have hh := W.field_bound k i hN _ (P.paidReference l) face (by positivity) (by simp [hf]) d mark hm hoff
      simpa only [Q,E,M,f,cost,fee,hf,Bool.false_eq_true,if_false,Int.cast_natCast] using hh.trans (hr l).2
  have hmixed := P.design.average_reference_bounds P.shape P.arcs P.valid _ hθ (fun u => firstMoment (Q u)) f fee cost
    E M (P.rates.length : ℝ) ε H
  have hg (u : Fin P.groups.flatten.length) :
      P.design.weightAt (foldedAngle w) (f u)=
      ∑ j : Fin P.cuts.length, (nodeSign j.val (scannedNode P.groups u) : ℝ)*(P.design.directionForm j.val).field (foldedAngle w) := by
    rw [P.order.node u]
    exact P.design.field_at_node P.shape P.arcs P.cuts.length P.valid P.slopes (P.order.rank u) _
  simp only [hg] at hmixed
  rw [P.design.faceEnergy_at w hi,P.design.faceFee_at P.shape P.arcs P.valid w hi hθ]
  exact hmixed

end PiPolynomialValues.SelectedSequence
