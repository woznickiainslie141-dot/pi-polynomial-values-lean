module

public import OddPiPowers.PolynomialValues.EvaluationPlan
public import OddPiPowers.PolynomialValues.Analysis.UnitBlockRate

/-! Uniform asymptotic estimates along any sequence of selected minors,
including a sequence selected at varying real conjugates. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod PrimeWindow Finset Filter Real
open scoped Topology

structure SelectedSequence (P : EvaluationPlan) where
  grid : ℕ → ℕ
  grow : Tendsto grid atTop atTop
  root : ℕ → ℂ
  witness : ∀ i, SelectedPolynomial P.shape P.groups (4*grid i) (root i) P.degreeA P.degreeB

namespace SelectedSequence

variable {P : EvaluationPlan} (W : SelectedSequence P)

def index (i : ℕ) := 4*W.grid i
def mass (i : ℕ) : ℝ := ((P.shape.massUnit*W.index i : ℕ) : ℝ)
def size (i : ℕ) := Fintype.card (Column (P.shape.band (W.index i)))
noncomputable def lengthRatio (i : ℕ) := (W.size i : ℝ)/W.mass i

theorem index_atTop : Tendsto W.index atTop atTop := W.grow.const_mul_atTop' (by decide : 0<4)
theorem mass_atTop : Tendsto W.mass atTop atTop := massScale_atTop W.index_atTop P.rows.mass_pos

theorem length_limit : Tendsto W.lengthRatio atTop (𝓝 (P.rates.length : ℝ)) := by
  rw [← P.width_eq]
  exact selected_length_limit W.index_atTop P.rows.mass_pos

theorem counts (v : Fin P.groups.flatten.length) :
    Tendsto (fun i => ((W.witness i).count v : ℝ)/W.mass i) atTop
      (𝓝 (rowRate P.shape (P.shape.ratioAt (scannedNode P.groups v)))) :=
  selected_mass_limit P.rows W.index_atTop W.witness v

theorem positive_rows : ∀ᶠ i in atTop, ∀ v, 0<(W.witness i).count v ∧ (W.witness i).count v≤W.size i :=
  selected_count_positive P.rows W.index_atTop W.witness

noncomputable def finiteReference {S : List ℤ} {p : ℤ} {B : ℚ} (E : ReferenceEvidence P.shape P.anchor S p B)
    (k i : ℕ) := referenceFiniteTerm P.shape E.rows E.positive P.anchor p (W.grid i)
      (fun j => ((W.witness i).count ((E.rowRank P.order).symm j) : ℝ)/W.mass i) (W.lengthRatio i) (innerRadius k)

theorem reference_eventual {S : List ℤ} {p : ℤ} {B : ℚ} (E : ReferenceEvidence P.shape P.anchor S p B)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ k in atTop, ∀ᶠ i in atTop, W.finiteReference E k i<(P.rates.length : ℝ)*B+ε := by
  let v := E.rowRank P.order
  have hm (j : Fin E.rows.length) : Tendsto (fun i => ((W.witness i).count (v.symm j) : ℝ)/W.mass i) atTop
      (𝓝 ((P.shape.massList[j.val]?.getD 0 : ℚ) : ℝ)) := by
    have he := P.order.mass_at (v.symm j)
    have hv : (P.order.rank (v.symm j)).val=j.val := congrArg Fin.val (v.apply_symm_apply j)
    rw [hv] at he
    rw [he]
    simpa only [Shape.rowMassQ,Rat.cast_div,Rat.cast_natCast,rowRate] using W.counts (v.symm j)
  have hL : 0<P.shape.totalWidthQ := (of_decide_eq_true P.base).1
  have hmass : Tendsto W.lengthRatio atTop (𝓝 (P.shape.totalWidthQ : ℝ)) := P.width_eq.symm ▸ W.length_limit
  have inner (k : ℕ) : Tendsto (W.finiteReference E k) atTop
      (𝓝 (referenceInnerTerm P.shape E.rows E.positive P.anchor p (innerRadius k))) :=
    referenceFiniteTerm_limit W.grow P.shape P.rowSum_pos P.width E.rows E.positive P.anchor p
      (innerRadius k) _ W.lengthRatio hm hmass
  apply twoStage_upper inner (referenceInnerTerm_limit P.shape P.width hL E.rows E.positive P.anchor p) _ hε
  rw [P.width_eq]
  exact mul_le_mul_of_nonneg_left E.cost P.length_pos.le

theorem tail_limit (j : Fin P.cuts.length) (face : Bool) :
    Tendsto (fun i => tailCap (W.witness i).count (scannedNode P.groups)
      (fun k => (bandFrequency P.shape (W.index i) (columnReflection _ face ((W.witness i).colIndex k)) : ℝ))
      (W.mass i) j.val ((P.cuts.get j).location P.shape)) atTop (𝓝 (2*(cutMomentQ P.shape (P.cuts.get j) : ℝ))) :=
  selected_tailCap_limit P.rows W.index_atTop W.witness P.width face (P.cuts.get j) j.val P.common (P.cut j) (P.mass j)

theorem overhead_limit (K : ℝ) (hK : 1≤K) (J V : ℕ) :
    Tendsto (fun i => (W.size i : ℝ)*(log V+columnOverhead K (W.size i) J)/(W.mass i)^2) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp W.mass_atTop
  have H := ((hi.const_mul (log V)).add (columnOverhead_limit J W.mass_atTop W.length_limit P.length_pos hK))
  simp only [mul_zero,zero_add] at H
  have HH := W.length_limit.mul H
  simp only [mul_zero] at HH
  apply HH.congr
  intro i
  change ((W.size i : ℝ)/W.mass i)*(log V*(W.mass i)⁻¹+columnOverhead K (W.size i) J/W.mass i)=_
  simp only [div_eq_mul_inv,← inv_pow]
  ring

end SelectedSequence
end PiPolynomialValues
