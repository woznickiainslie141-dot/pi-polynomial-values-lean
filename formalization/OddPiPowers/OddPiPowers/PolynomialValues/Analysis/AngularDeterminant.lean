module

public import OddPiPowers.PolynomialValues.Analysis.ZeroAllocation

/-! A boundary inequality for the actual centered Taylor minor, uniform
in the maximizing permutation. The two tail bounds are combined before
the Poisson integration. -/

@[expose] public section

namespace PiPolynomialValues.SelectedSequence

open FourPeriod Finset Polynomial Real Filter
open scoped Topology

variable {P : EvaluationPlan} (W : SelectedSequence P)

def frequency (i : ℕ) (c : Fin (W.size i)) : ℤ := ((W.witness i).colIndex c).2.val
def layer (i : ℕ) (c : Fin (W.size i)) := ((W.witness i).colIndex c).1.val

noncomputable def minor (i : ℕ) (h : LabelChoice (W.layer i)) (p : Fin P.groups.flatten.length → ℂ) :=
  (centeredLabelMatrix (W.witness i).rowIndex (scannedNode P.groups) (W.frequency i) (W.layer i)
    (centeredGridValue P.shape P.anchor (W.grid i)) h p).det

noncomputable def tail (i : ℕ) (face : Bool) (j : Fin P.cuts.length) :=
  tailCap (W.witness i).count (scannedNode P.groups) (fun c => (W.columns i face c : ℝ))
    (W.mass i) j.val ((P.cuts.get j).location P.shape)

noncomputable def bothTails (i : ℕ) (j : Fin P.cuts.length) := max (W.tail i false j) (W.tail i true j)

theorem tail_le_both (i : ℕ) (face : Bool) (j : Fin P.cuts.length) : W.tail i face j≤W.bothTails i j := by
  cases face
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem bothTails_limit (j : Fin P.cuts.length) : Tendsto (fun i => W.bothTails i j) atTop
    (𝓝 (2*(cutMomentQ P.shape (P.cuts.get j) : ℝ))) := by
  have H (face : Bool) : Tendsto (fun i => W.tail i face j) atTop
      (𝓝 (2*(cutMomentQ P.shape (P.cuts.get j) : ℝ))) := W.tail_limit j face
  have h := (H false).max (H true)
  rw [max_self] at h
  exact h

noncomputable def gapTail (i : ℕ) (a : Fin P.cuts.length → ℝ) := ∑ j, a j*W.bothTails i j

theorem gapTail_limit (a : Fin P.cuts.length → ℝ) : Tendsto (fun i => W.gapTail i a) atTop
    (𝓝 (∑ j, a j*(2*(cutMomentQ P.shape (P.cuts.get j) : ℝ)))) :=
  tendsto_finsetSum univ (fun j _ => (W.bothTails_limit j).const_mul (a j))

theorem angular_det_bound (i k : ℕ) (hm : ∀ u, 0<(W.witness i).count u ∧ (W.witness i).count u≤W.size i)
    (hN : 2≤W.mass i) {ε : ℝ} (hfit : W.referencesFit k i ε) {r t : ℝ} (hr : 0<r) (ht : 0≤t) (ht1 : t<1)
    (g : Fin P.cuts.length → ℂ[X]) (hg : ∀ j, ((g j).eval (r : ℂ)).im=0) (hgap : ∀ j, 0≤pathGap r (g j))
    (h : LabelChoice (W.layer i)) (z : ℂ) (hz : ‖z‖=1) (hi : z.im≠0)
    (hθ : P.design.weightAt (foldedAngle z) (fun _ => 1)=1) {K : ℝ} (hK : 1≤K)
    (hv : ∀ u c, ‖(scannedNode P.groups u : ℂ)-(centeredGridValue P.shape P.anchor (W.grid i) (W.frequency i c) : ℂ)‖≤K)
    (hp : ∀ u, ‖incrementFamily r t g (scannedNode P.groups u) z‖≤K) :
    let V := P.groups.flatten.length
    let n := W.size i
    let N := W.mass i
    let p u := incrementFamily r t g (scannedNode P.groups u) z
    let blocks := ∑ u, blockScaleCost N (innerRadius k) ((W.witness i).count u)
    ‖W.minor i h p‖≤exp ((n : ℝ)*(log V+columnOverhead K n P.shape.widths.length)+N^2*
      (blocks+(P.rates.length : ℝ)*P.design.faceEnergy z+ε-
        markedMass (fun c => (h c).val) N*P.design.faceFee z+
        slopeError g (fun j => P.design.directionForm j.val) z*W.lengthRatio i+
        |(correctionPath r t z).im| * W.gapTail i (fun j => pathGap r (g j)))) := by
  intro V n N p blocks
  by_cases hn : W.minor i h p=0
  · rw [hn,norm_zero]; exact (exp_pos _).le
  let w := W.witness i
  let f := upperSide z
  let v := scannedNode P.groups
  let a (j : Fin P.cuts.length) := pathGap r (g j)
  let b := |(correctionPath r t z).im|
  let G (u : Fin V) := ∑ j : Fin P.cuts.length, (nodeSign j.val (v u) : ℝ)*(P.design.directionForm j.val).field (foldedAngle z)
  let err := slopeError g (fun j => P.design.directionForm j.val) z
  have hpos : 0<N := by dsimp only [N]; linarith
  have hε : 0≤err := sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨θ,hoff,H⟩ := determinant_allocated_rate w.rowIndex P.groups_pos hm v (W.frequency i) (W.layer i)
    (fun c => (w.colIndex c).1.isLt.le) (centeredGridValue P.shape P.anchor (W.grid i)) h p hK hv hp hN
    (innerRadius_bounds k).1 (innerRadius_bounds k).2 f (W.columns i f) (W.columns_value hpos f) hn
  let d := allocationEquiv w.rowIndex θ
  let Q := W.charge i f d
  have hm' (c : Fin n) : (h c).val≤(w.colIndex c).1.val := Nat.lt_succ_iff.mp (h c).isLt
  have hmix := W.mixed_field_bound k i hpos hfit z hi hθ d (fun c => (h c).val) hm' hoff
  have hlin := boundary_allocation_bound w.count d (W.columns i f) hpos v (fun u => faceSlope f (p u)) G
    (fun j => a j*b) (fun j => (P.cuts.get j).location P.shape) (fun j => mul_nonneg (hgap j) (abs_nonneg _))
    hε (fun u => family_slope_error hr ht ht1 g hg _ z hz hi (v u))
  have htail : (∑ j, a j*b*W.tail i f j)≤b*W.gapTail i a := by
    rw [gapTail,mul_sum]
    exact sum_le_sum (fun j _ => (mul_le_mul_of_nonneg_left (W.tail_le_both i f j)
      (mul_nonneg (hgap j) (abs_nonneg _))).trans_eq (by ring))
  change (∑ u, firstMoment (Q u)*G u)+(∑ u, radialSelf (innerRadius k) (Q u)/2)+
    markedMass (fun c => (h c).val) N*P.design.faceFee z≤_ at hmix
  change (∑ u, Q u (linearFrequency (faceSlope f (p u))))≤
    (∑ u, firstMoment (Q u)*G u)+(∑ j, a j*b*W.tail i f j)+err*W.lengthRatio i at hlin
  apply H.trans
  rw [exp_le_exp]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [sum_add_distrib,sum_add_distrib]
  change blocks+(∑ u, Q u (linearFrequency (faceSlope f (p u))))+(∑ u, radialSelf (innerRadius k) (Q u)/2)≤_
  linarith only [hlin,hmix,htail]

end PiPolynomialValues.SelectedSequence
