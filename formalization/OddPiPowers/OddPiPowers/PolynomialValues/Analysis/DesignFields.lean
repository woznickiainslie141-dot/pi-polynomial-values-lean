module

public import OddPiPowers.PolynomialValues.Analysis.IncrementPaths
public import OddPiPowers.PolynomialValues.Analysis.SelectedReference
public import OddPiPowers.PolynomialValues.Analysis.DirectionMoments
public import OddPiPowers.PolynomialValues.Numerics.LabelReferences

/-! Decode the same signed row slope from an angular label, the density
certificate and the adjacent increments of an analytic row path. -/

@[expose] public section

namespace PiPolynomialValues

open Finset FourPeriod

def signedLabelSlope (t : AngleLabel) (i : ℕ) : ℚ :=
  (((signedSlopes t.slopes)[i]?.getD 0 : ℤ) : ℚ)/100000

def AngleDesign.fieldTest (D : AngleDesign) (s : Shape) (K : ℕ) : Bool := decide
  ((∀ i : Fin s.rows.length, (∑ k : Fin K, nodeSign k.val (signedNode s i))=signedNode s i) ∧
   (D.labels.all fun t => decide (∀ i : Fin s.rows.length, signedLabelSlope t i.val=
     ∑ k : Fin K, (nodeSign k.val (signedNode s i) : ℚ)*(t.slope (k.val+1)-t.slope k.val)))=true)

theorem signedLabelSlope_of_evidence {s : Shape} {a : AnchorPlan} {t : AngleLabel} {p : ℤ} {B : ℚ}
    (E : ReferenceEvidence s a t.slopes p B) (i : Fin E.rows.length) :
    (signedLabelSlope t i.val : ℝ)=((E.rows.get i).slope : ℝ)/100000 := by
  unfold signedLabelSlope
  rw [← E.field]
  simp [List.getElem?_map,List.getElem?_eq_getElem i.isLt]

theorem AngleDesign.weightAt_congr (D : AngleDesign) (s : Shape) (arcs : List ArcRow) (h : D.valid s arcs=true)
    (θ : ℝ) {f g : AngleLabel → ℝ} (he : ∀ t∈D.labels, f t=g t) : D.weightAt θ f=D.weightAt θ g :=
  le_antisymm (D.weightAt_mono s arcs h θ (fun t ht => (he t ht).le))
    (D.weightAt_mono s arcs h θ (fun t ht => (he t ht).ge))

private theorem weighted_finite_sum {A K : Type*} [Fintype A] [Fintype K] (w : A → ℝ) (a : K → ℝ) (v : A → K → ℝ) :
    (∑ i, w i*(∑ k, a k*v i k))=∑ k, a k*(∑ i, w i*v i k) := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by ring))

theorem AngleDesign.weightAt_sum {K : Type*} [Fintype K] (D : AngleDesign) (θ : ℝ)
    (a : K → ℝ) (f : K → AngleLabel → ℝ) :
    D.weightAt θ (fun t => ∑ k, a k*f k t)=∑ k, a k*D.weightAt θ (f k) := by
  simp only [weightAt,realMix,list_field_sum]
  have H (i : Fin D.cells.length) := weighted_finite_sum
    (fun j : Fin (D.cells.get i).parts.length => (((D.cells.get i).parts.get j).2 : ℝ)) a
    (fun j k => f k (D.labels[((D.cells.get i).parts.get j).1]?.getD default))
  simp only [H]
  apply weighted_finite_sum

theorem AngleDesign.field_at_node (D : AngleDesign) (s : Shape) (arcs : List ArcRow) (K : ℕ)
    (hd : D.valid s arcs=true) (he : D.fieldTest s K=true) (i : Fin s.rows.length) (θ : ℝ) :
    D.weightAt θ (fun t => (signedLabelSlope t i.val : ℝ))=
      ∑ k : Fin K, (nodeSign k.val (signedNode s i) : ℝ)*(D.directionForm k.val).field θ := by
  have hM := (of_decide_eq_true he).2
  have h (t : AngleLabel) (ht : t∈D.labels) : (signedLabelSlope t i.val : ℝ)=
      ∑ k : Fin K, (nodeSign k.val (signedNode s i) : ℝ)*((t.slope (k.val+1)-t.slope k.val : ℚ) : ℝ) := by
    have H := congrArg (fun q : ℚ => (q : ℝ)) (of_decide_eq_true (List.all_eq_true.mp hM t ht) i)
    simpa only [Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast] using H
  rw [D.weightAt_congr s arcs hd θ h,D.weightAt_sum]
  exact sum_congr rfl (fun k _ => congrArg (fun x : ℝ => (nodeSign k.val (signedNode s i) : ℝ)*x)
    (D.weightAt_form (fun t => t.slope (k.val+1)-t.slope k.val) θ))

end PiPolynomialValues
