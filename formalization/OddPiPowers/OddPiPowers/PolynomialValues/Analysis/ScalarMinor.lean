module

public import OddPiPowers.PolynomialValues.Analysis.PrimaryMinorRate

/-! At a secondary conjugate the scalar correction alone supplies the
prescribed phases. Both faces use the zero-slope spatial certificate. -/

@[expose] public section

namespace PiPolynomialValues.SelectedSequence

open FourPeriod Finset Filter Real Polynomial MeasureTheory
open scoped Topology

variable {P : EvaluationPlan} (W : SelectedSequence P)

noncomputable def scalarPath (P : EvaluationPlan) (r t : ℝ) (v : ℤ) :=
  incrementFamily (K := P.cuts.length) r t (fun _ => (0 : ℂ[X])) v

theorem scalar_slope {P : EvaluationPlan} {r t : ℝ} (hr : 0<r) (ht : 0≤t) (ht1 : t<1)
    (w : ℂ) (hw : ‖w‖=1) (hi : w.im≠0) (v : ℤ) :
    |faceSlope (upperSide w) (scalarPath P r t v w)-0-
       orderedDirection (fun _ : Fin P.cuts.length => π/2*|(correctionPath r t w).im|) v|≤0 := by
  have H := family_slope_error (K := P.cuts.length) hr ht ht1 (fun _ => (0 : ℂ[X])) (fun _ => by simp)
    (fun _ => ([] : ArcForm)) w hw hi v
  simpa [scalarPath,slopeError,pathGap,ArcForm.field,signedFold] using H

theorem scalar_boundary (i k : ℕ) (hm : ∀ u, 0<(W.witness i).count u ∧ (W.witness i).count u≤W.size i)
    (hN : 2≤W.mass i) {r t : ℝ} (hr : 0<r) (ht : 0≤t) (ht1 : t<1)
    (E : ReferenceEvidence P.shape P.anchor (List.replicate P.shape.ratios.length 0) 0 P.rates.ordinary)
    (h : LabelChoice (W.layer i)) (z : ℂ) (hz : ‖z‖=1) (hi : z.im≠0) {K : ℝ} (hK : 1≤K)
    (hv : ∀ u c, ‖(scannedNode P.groups u : ℂ)-(centeredGridValue P.shape P.anchor (W.grid i) (W.frequency i c) : ℂ)‖≤K)
    (hp : ∀ u, ‖scalarPath P r t (scannedNode P.groups u) z‖≤K) :
    let N := W.mass i
    let n := W.size i
    let p u := scalarPath P r t (scannedNode P.groups u) z
    let blocks := ∑ u, blockScaleCost N (innerRadius k) ((W.witness i).count u)
    ‖W.minor i h p‖≤exp ((n : ℝ)*(log P.groups.flatten.length+columnOverhead K n P.shape.widths.length)+N^2*
      (blocks+W.finiteReference E k i+|(correctionPath r t z).im| * W.gapTail i (fun _ => π/2))) := by
  intro N n p blocks
  by_cases hn : W.minor i h p=0
  · rw [hn,norm_zero]; exact (exp_pos _).le
  let w := W.witness i
  let f := upperSide z
  let v := scannedNode P.groups
  let b := |(correctionPath r t z).im|
  have hpos : 0<N := by dsimp only [N]; linarith
  obtain ⟨θ,_,H⟩ := determinant_allocated_rate w.rowIndex P.groups_pos hm v (W.frequency i) (W.layer i)
    (fun c => (w.colIndex c).1.isLt.le) (centeredGridValue P.shape P.anchor (W.grid i)) h p hK hv hp hN
    (innerRadius_bounds k).1 (innerRadius_bounds k).2 f (W.columns i f) (W.columns_value hpos f) hn
  let d := allocationEquiv w.rowIndex θ
  let Q := W.charge i f d
  have hself := W.zero_reference_bound k i hpos E f d
  have hlin := boundary_allocation_bound w.count d (W.columns i f) hpos v (fun u => faceSlope f (p u)) (fun _ => 0)
    (fun _ : Fin P.cuts.length => π/2*b) (fun j => (P.cuts.get j).location P.shape)
    (fun _ => mul_nonneg (by positivity) (abs_nonneg _)) (le_refl (0 : ℝ))
    (fun u => scalar_slope hr ht ht1 z hz hi (v u))
  have htail : (∑ j, π/2*b*W.tail i f j)≤b*W.gapTail i (fun _ => π/2) := by
    rw [gapTail,mul_sum]
    exact sum_le_sum (fun j _ => (mul_le_mul_of_nonneg_left (W.tail_le_both i f j)
      (mul_nonneg (by positivity) (abs_nonneg _))).trans_eq (by ring))
  simp only [mul_zero,sum_const_zero,zero_add,zero_mul,add_zero] at hlin
  apply H.trans
  rw [exp_le_exp]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [sum_add_distrib,sum_add_distrib]
  change blocks+(∑ u, Q u (linearFrequency (faceSlope f (p u))))+(∑ u, radialSelf (innerRadius k) (Q u)/2)≤_
  linarith only [show (∑ u, Q u (linearFrequency (faceSlope f (p u))))≤∑ j, π/2*b*W.tail i f j from hlin,htail,hself]

theorem scalar_sample {r t : ℝ} (hr : 0<r) (hr1 : r<1) (ht : 0≤t) (ht1 : t<1) (i k : ℕ)
    (hm : ∀ u, 0<(W.witness i).count u ∧ (W.witness i).count u≤W.size i) (hN : 2≤W.mass i)
    (E : ReferenceEvidence P.shape P.anchor (List.replicate P.shape.ratios.length 0) 0 P.rates.ordinary)
    {K : ℝ} (hK : 1≤K)
    (hv : ∀ u c, ‖(scannedNode P.groups u : ℂ)-(centeredGridValue P.shape P.anchor (W.grid i) (W.frequency i c) : ℂ)‖≤K)
    (hp : ∀ u z, ‖z‖=1 → ‖scalarPath P r t (scannedNode P.groups u) z‖≤K) (h : LabelChoice (W.layer i)) :
    let H := (W.size i : ℝ)*(log P.groups.flatten.length+columnOverhead K (W.size i) P.shape.widths.length)
    let B := ∑ u, blockScaleCost (W.mass i) (innerRadius k) ((W.witness i).count u)
    ∃ q : LabelChoice (fun c => (h c).val), ‖W.minor i h (fun u => phasePoint (scannedNode P.groups u))‖≤exp
      (((W.order i : ℝ)-labelPairs (fun c => (q c).val))*log (1/r)+
       (H+(W.mass i)^2*(B+W.finiteReference E k i+correctionMean r t*W.gapTail i (fun _ => π/2)))+1) := by
  intro H B
  have hr' : ‖(r : ℂ)‖<1 := by simpa [abs_of_pos hr] using hr1
  have hc : HasPoissonMean r (fun w => |(correctionPath r t w).im|) (correctionMean r t) := ⟨correction_integrable hr' ht ht1,rfl⟩
  have hb := (HasPoissonMean.constant hr' H).add (((HasPoissonMean.constant hr' (B+W.finiteReference E k i)).add
    (hc.right_mul (W.gapTail i (fun _ => π/2)))).left_mul ((W.mass i)^2))
  apply W.interior_mean i h hr hr1 _ (P.paths hr ht ht1 (fun _ => (0 : ℂ[X])) (fun _ => by simp)) hb
  filter_upwards [poissonLaw_unit r,imaginary_nonzero_ae hr hr1] with z hz hi
  exact W.scalar_boundary i k hm hN hr ht ht1 E h z hz hi hK hv (fun u => hp u z hz)

end PiPolynomialValues.SelectedSequence
