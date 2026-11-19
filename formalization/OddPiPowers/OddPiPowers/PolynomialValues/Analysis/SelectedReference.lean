module

public import OddPiPowers.PolynomialValues.Analysis.ReflectedColumns
public import OddPiPowers.PolynomialValues.Analysis.ReferenceLimits
public import OddPiPowers.PolynomialValues.Analysis.SelectedEvaluation

/-! The price obtained from the genuine determinant allocation uses the
same grid cell and the same center as the tabulated reference field. -/

@[expose] public section

namespace PiPolynomialValues

open Finset FourPeriod

noncomputable def centeredGridValue (s : Shape) (a : AnchorPlan) (t : ℕ) (x : ℤ) : ℤ :=
  (a.center (physicalCell (s.rows.sum*t) x) : ℤ)-(s.ratios.length-1 : ℕ)

def ReferenceEvidence.rowRank {s : Shape} {g : List (List ℤ)} {a : AnchorPlan} {S : List ℤ} {p : ℤ} {B : ℚ}
    (E : PiPolynomialValues.ReferenceEvidence s a S p B) (order : ScanOrder s g) : Fin g.flatten.length ≃ Fin E.rows.length :=
  order.rank.trans (finCongr E.rowCount.symm)

theorem ReferenceEvidence.rank_node {s : Shape} {g : List (List ℤ)} {a : AnchorPlan} {S : List ℤ} {p : ℤ} {B : ℚ}
    (E : PiPolynomialValues.ReferenceEvidence s a S p B) (order : ScanOrder s g) (v : Fin g.flatten.length) :
    scannedNode g v=((E.rowRank order v).val : ℤ)-(s.ratios.length-1 : ℕ) := order.node v

theorem selected_reference_bound {s : Shape} {g : List (List ℤ)} {a : AnchorPlan} {S : List ℤ} {p : ℤ} {B : ℚ}
    (E : PiPolynomialValues.ReferenceEvidence s a S p B) (order : ScanOrder s g) (hw : ∀ w∈s.widths, w≤10000)
    {t n : ℕ} (hN : 0 < s.massUnit*(4*t)) (m : Fin g.flatten.length → ℕ)
    (d : ((v : Fin g.flatten.length) × Fin (m v)) ≃ Fin n) (e : Fin n ≃ Column (s.band (4*t)))
    (face : Bool) (hp : 0≤p) (hface : face=true → p=0) (mark : Fin n → ℕ)
    (hmark : ∀ c, mark c≤(e c).1.val)
    (hoff : ∀ v i, mark (d ⟨v,i⟩)≠0 → scannedNode g v≠centeredGridValue s a t (e (d ⟨v,i⟩)).2.val)
    {r : ℝ} (hr : 0≤r) (hr1 : r<1) :
    let N := ((s.massUnit*(4*t) : ℕ) : ℝ)
    let y (i : Fin n) := bandFrequency s (4*t) (columnReflection _ face (e i))
    let P := allocationCharge m d y N
    let v := E.rowRank order
    (∑ u, (P u (linearFrequency (((E.rows.get (v u)).slope : ℝ)/100000))+radialSelf r (P u)/2))+
      N⁻¹*(∑ c, if mark c=0 then 0 else (p : ℝ)/10^7)≤
        referenceFiniteTerm s E.rows E.positive a p t (fun j => (m (v.symm j) : ℝ)/N) ((n : ℝ)/N) r := by
  intro N y P v
  let c := e.trans (columnReflection _ face)
  let fee (i : Fin n) : ℝ := if mark i=0 then 0 else (p : ℝ)/10^7
  let G (i : Fin n) : ℝ := layerCellField E.rows E.positive a p (c i).1.val
    (physicalCell (s.rows.sum*t) (c i).2.val) (y i : ℝ)
  have hv : 0 < g.flatten.length := by
    have he := Fintype.card_congr v
    simp only [Fintype.card_fin] at he
    exact he.symm ▸ E.positive
  have hg (u : Fin g.flatten.length) (i : Fin (m u)) :
      (E.rows.get (v u)).realField (y (d ⟨u,i⟩) : ℝ)+fee (d ⟨u,i⟩)≤G (d ⟨u,i⟩) := by
    let j := d ⟨u,i⟩
    change (E.rows.get (v u)).realField (y j : ℝ)+fee j≤G j
    have h := columnPriceSum_envelope E.rows E.positive a hp (c j).1.val
      (physicalCell (s.rows.sum*t) (c j).2.val) (y j : ℝ) (v u)
    apply (add_le_add le_rfl ?_).trans h
    by_cases h₀ : mark j=0
    · simp only [fee,h₀,if_true]
      split_ifs <;> positivity
    · by_cases hf : face=true
      · simp [fee,hface hf]
      · have hface' : face=false := Bool.eq_false_of_not_eq_true hf
        have hc : c j=e j := by simp [c,hface',columnReflection]
        have h₁ : (c j).1.val≠0 := by rw [hc]; have hh := hmark j; omega
        have h₂ : a.center (physicalCell (s.rows.sum*t) (c j).2.val)≠(v u).val := by
          intro he
          apply hoff u i h₀
          rw [E.rank_node order u]
          change ((v u).val : ℤ)-_=_
          rw [← he,hc]
          rfl
        simp [fee,h₀,h₁,h₂]
  have H := reference_allocation_bound m hv d y (show 0 < N by dsimp only [N]; exact_mod_cast hN) hr hr1 E.rows E.checked
    v s hw G fee hg
  dsimp only at H
  have hP : (∑ u, P u)=bandCharge s (4*t) := allocatedBandCharge m d e face
  have hG : N⁻¹*(∑ j, G j)=columnPriceSum s E.rows E.positive a p t := by
    have he := c.sum_comp (fun j => layerCellField E.rows E.positive a p j.1.val
      (physicalCell (s.rows.sum*t) j.2.val) ((j.2.val : ℝ)*N⁻¹))
    simpa only [G,y,c,Equiv.trans_apply,bandFrequency_value s hw hN,columnPriceSum,N] using congrArg (fun x : ℝ => N⁻¹*x) he
  let Q (j : Fin E.rows.length) := laneCharge (E.rows.get j)
  have hRows := v.sum_comp (fun j => (m (v.symm j) : ℝ)/N*(((E.rows.get j).β : ℝ)/100000)-radialSelf r (Q j)/2)
  simp only [Equiv.symm_apply_apply] at hRows
  have hLen := Fintype.card_congr v
  simp only [Fintype.card_fin] at hLen
  change (∑ u, (P u _+radialSelf r (P u)/2))≤N⁻¹*((∑ j, G j)-(∑ j, fee j)+(n : ℝ)*_) +
    (∑ u, ((m u : ℝ)/N*(((E.rows.get (v u)).β : ℝ)/100000)-radialSelf r (Q (v u))/2))+
    (2*((∑ u, P u)-fullBandCharge s) (radialPotential unitFrequency r (remainderCharge s E.rows))+
      radialSelf r (remainderCharge s E.rows))/(2*g.flatten.length) at H
  have hLen' : (g.flatten.length : ℝ)=(E.rows.length : ℝ) := by exact_mod_cast hLen
  rw [hP,hRows,hLen'] at H
  unfold referenceFiniteTerm referenceRowsTerm
  rw [← hG]
  change _+N⁻¹*(∑ j, fee j)≤_
  dsimp only [Q] at H
  simp only [div_eq_mul_inv] at H ⊢
  linarith only [H]

end PiPolynomialValues
