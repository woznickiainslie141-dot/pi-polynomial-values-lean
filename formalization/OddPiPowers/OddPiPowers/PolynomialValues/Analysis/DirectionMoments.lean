module

public import OddPiPowers.PolynomialValues.Numerics.AngleMixture
public import OddPiPowers.PolynomialValues.Analysis.ResidualCharge

/-! Evaluate the correction for adjacent signed slopes with the actual
boundary weights. The finite test compares the two rational ways of
assigning the tail moments to the angular labels. -/

@[expose] public section

namespace PiPolynomialValues

open Finset FourPeriod

noncomputable def AngleDesign.average (D : AngleDesign) (z : ℚ) (sine : Bool) (f : AngleLabel → ℝ) : ℝ :=
  ∑ i : Fin D.cells.length, ((D.cells.get i).arc.boundaryWeight z sine)*
    ∑ j : Fin (D.cells.get i).parts.length, (((D.cells.get i).parts.get j).2 : ℝ)*
       f (D.labels[((D.cells.get i).parts.get j).1]?.getD default)

theorem AngleDesign.average_form (D : AngleDesign) (z : ℚ) (sine : Bool) (f : AngleLabel → ℚ) :
    D.average z sine (fun t => (f t : ℝ))=(D.form f).actual z sine := by
  unfold average form ArcForm.actual
  simp only [List.map_map,Function.comp_apply,Function.comp_def]
  rw [list_field_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_comm]
  congr 1
  unfold mix
  rw [Rat.cast_list_sum,List.map_map,list_field_sum]
  simp only [Function.comp_def,Rat.cast_mul]

theorem AngleDesign.average_congr (D : AngleDesign) (s : Shape) (arcs : List ArcRow) (hd : D.valid s arcs=true)
    (z : ℚ) (sine : Bool) {f g : AngleLabel → ℝ} (h : ∀ t∈D.labels, f t=g t) :
    D.average z sine f=D.average z sine g := by
  have hh := (of_decide_eq_true hd).2.1
  unfold average
  apply sum_congr rfl
  intro i _
  congr 1
  apply sum_congr rfl
  intro j _
  congr 1
  have H := (of_decide_eq_true (List.all_eq_true.mp hh (D.cells.get i) (List.get_mem _ _))).2
  have hp := (of_decide_eq_true (List.all_eq_true.mp H _ (List.get_mem _ j))).1
  rw [List.getElem?_eq_getElem hp,Option.getD_some]
  exact h _ (List.getElem_mem hp)

private theorem weighted_exchange {A K : Type*} [Fintype A] [Fintype K] (w : A → ℝ) (a : K → ℝ) (v : A → K → ℝ) :
    (∑ i, w i*(∑ k, a k*v i k))=∑ k, a k*(∑ i, w i*v i k) := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl (fun k _ => sum_congr rfl (fun i _ => by ring))

theorem AngleDesign.average_sum {K : Type*} [Fintype K] (D : AngleDesign) (z : ℚ) (sine : Bool)
    (a : K → ℝ) (f : K → AngleLabel → ℝ) :
    D.average z sine (fun t => ∑ k, a k*f k t)=∑ k, a k*D.average z sine (f k) := by
  unfold average
  have H (i : Fin D.cells.length) := weighted_exchange
    (fun j : Fin (D.cells.get i).parts.length => (((D.cells.get i).parts.get j).2 : ℝ)) a
    (fun j k => f k (D.labels[((D.cells.get i).parts.get j).1]?.getD default))
  simp only [H]
  apply weighted_exchange

def cutWeight (s : Shape) (cuts : List QuantileCut) (d : RateData) (k : Fin cuts.length) := 2*cutMomentQ s (cuts.get k)/d.length

def AngleDesign.momentTest (D : AngleDesign) (s : Shape) (cuts : List QuantileCut) (d : RateData) : Bool := decide
  ((∑ k, cutWeight s cuts d k)=d.moment ∧
   (D.labels.all fun t => decide (-2*t.fieldMoment (upperNodeMoments s cuts)/d.length =
      ∑ k : Fin cuts.length, -(cutWeight s cuts d k)*(t.slope (k.val+1)-t.slope k.val)))=true)

theorem AngleDesign.direction_moments (D : AngleDesign) (s : Shape) (cuts : List QuantileCut) (d : RateData)
    (arcs : List ArcRow) (hd : D.valid s arcs=true) (hm : D.momentTest s cuts d=true) (A : ℝ) :
    (∑ k : Fin cuts.length, (cutWeight s cuts d k : ℝ)*(A-(D.directionForm k.val).actual d.radius true))=
      A*(d.moment : ℝ)+(D.sineForm (upperNodeMoments s cuts) d.length).actual d.radius true := by
  obtain ⟨hW,hM⟩ := of_decide_eq_true hm
  let v (k : Fin cuts.length) (t : AngleLabel) := t.slope (k.val+1)-t.slope k.val
  let a (k : Fin cuts.length) := -(cutWeight s cuts d k : ℝ)
  have h (t : AngleLabel) (ht : t∈D.labels) :
      ((-2*t.fieldMoment (upperNodeMoments s cuts)/d.length : ℚ) : ℝ)=∑ k, a k*(v k t : ℝ) := by
    have he := congrArg (fun q : ℚ => (q : ℝ)) (of_decide_eq_true (List.all_eq_true.mp hM t ht))
    simpa only [Rat.cast_sum,Rat.cast_mul,Rat.cast_neg,a,v] using he
  have H := D.average_congr s arcs hd d.radius true h
  rw [D.average_sum] at H
  simp only [D.average_form] at H
  have hW' : (∑ k, (cutWeight s cuts d k : ℝ))=(d.moment : ℝ) := by exact_mod_cast hW
  change (D.sineForm (upperNodeMoments s cuts) d.length).actual d.radius true=
    ∑ k : Fin cuts.length, a k*(D.directionForm k.val).actual d.radius true at H
  rw [H]
  simp only [mul_sub,sum_sub_distrib,← sum_mul,hW',a,neg_mul,sum_neg_distrib]
  ring

end PiPolynomialValues
