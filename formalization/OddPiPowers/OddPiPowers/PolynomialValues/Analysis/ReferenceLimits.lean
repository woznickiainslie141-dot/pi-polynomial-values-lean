module

public import OddPiPowers.PolynomialValues.Analysis.ReferenceAllocation
public import OddPiPowers.PolynomialValues.Analysis.ReferenceGridLimit
public import OddPiPowers.PolynomialValues.Analysis.SelectedScaleLimits
public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence

/-! First let the true band scale grow at a fixed smoothing radius, then
let that radius tend to one. Both upper bounds are independent of the
allocation of columns and the values of the boundary paths. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Filter FourPeriod
open scoped Topology

noncomputable def remainderCharge (s : Shape) (rows : List SpatialLane) :=
  meshReference (n := 80001) (step := 1) (by decide) (residualJump rows s.widths)

noncomputable def radialSelf (r : ℝ) (Q : ContinuousCharge FrequencyInterval) :=
  radialInteraction unitFrequency r Q Q

noncomputable def referenceRowsTerm (rows : List SpatialLane) (r : ℝ) (mass : Fin rows.length → ℝ) :=
  ∑ j, (mass j*(((rows.get j).β : ℝ)/100000)-radialSelf r (laneCharge (rows.get j))/2)

noncomputable def referenceFiniteTerm (s : Shape) (rows : List SpatialLane) (hn : 0 < rows.length) (a : AnchorPlan)
    (p : ℤ) (t : ℕ) (mass : Fin rows.length → ℝ) (ell r : ℝ) :=
  columnPriceSum s rows hn a p t+ell*referenceRadialError rows r+referenceRowsTerm rows r mass+
    (2*(bandCharge s (4*t)-fullBandCharge s) (radialPotential unitFrequency r (remainderCharge s rows))+
      radialSelf r (remainderCharge s rows))/(2*rows.length)

noncomputable def referenceInnerTerm (s : Shape) (rows : List SpatialLane) (hn : 0 < rows.length) (a : AnchorPlan)
    (p : ℤ) (r : ℝ) :=
  (∑ i ∈ range 80000, cellValue rows hn s.widths a p i)+(s.totalWidthQ : ℝ)*referenceRadialError rows r+
    referenceRowsTerm rows r (fun j => (s.massList[j.val]?.getD 0 : ℚ))+
    radialSelf r (remainderCharge s rows)/(2*rows.length)

theorem referenceFiniteTerm_limit {ι : Type*} {F : Filter ι} {t : ι → ℕ} (ht : Tendsto t F atTop)
    (s : Shape) (hs : 0 < s.rows.sum) (hw : ∀ w∈s.widths, w≤10000) (rows : List SpatialLane)
    (hn : 0 < rows.length) (a : AnchorPlan) (p : ℤ) (r : ℝ) (mass : ι → Fin rows.length → ℝ) (ell : ι → ℝ)
    (hm : ∀ j, Tendsto (fun i => mass i j) F (𝓝 ((s.massList[j.val]?.getD 0 : ℚ) : ℝ)))
    (hl : Tendsto ell F (𝓝 (s.totalWidthQ : ℝ))) :
    Tendsto (fun i => referenceFiniteTerm s rows hn a p (t i) (mass i) (ell i) r) F
      (𝓝 (referenceInnerTerm s rows hn a p r)) := by
  have hN : 0 < s.massUnit := by unfold Shape.massUnit; positivity
  have hG := (columnPriceSum_limit s hs hw rows hn a p).comp ht
  have hP := (bandCharge_residual_limit s hN (remainderCharge s rows) r).comp (ht.const_mul_atTop' (by decide : 0<4))
  have hQ := tendsto_finsetSum (univ : Finset (Fin rows.length)) (fun j _ =>
    ((hm j).mul_const (((rows.get j).β : ℝ)/100000)).sub_const (radialSelf r (laneCharge (rows.get j))/2))
  have hR := ((hP.const_mul 2).add_const (radialSelf r (remainderCharge s rows))).div_const (2*(rows.length : ℝ))
  simpa only [referenceFiniteTerm,referenceInnerTerm,referenceRowsTerm,Function.comp_apply,mul_zero,zero_add] using
    (((hG.add (hl.mul_const (referenceRadialError rows r))).add hQ).add hR)

theorem mesh_radialSelf_limit {n step : ℕ} (h : (n-1)*step≤80000) (d : ℕ → ℤ) :
    Tendsto (fun k => radialSelf (innerRadius k) (meshReference h d)) atTop
      (𝓝 (meshReference h d (meshLimitPotential h d))) :=
  ((meshReference h d).continuous.tendsto _).comp (meshReference_radial_limit h d
    (fun k => (innerRadius_bounds k).1) (fun k => (innerRadius_bounds k).2) innerRadius_tendsto)

attribute [local irreducible] meshReference meshLimitPotential

private theorem transport_self_limit (P Q : ContinuousCharge FrequencyInterval) (f g : C(FrequencyInterval,ℝ))
    (hP : P=Q) (hf : f=g) (h : Tendsto (fun k => radialSelf (innerRadius k) Q) atTop (𝓝 (Q g))) :
    Tendsto (fun k => radialSelf (innerRadius k) P) atTop (𝓝 (P f)) := by rw [hP,hf]; exact h

private theorem fine_self_limit (d : ℕ → ℤ) : Tendsto (fun k => radialSelf (innerRadius k)
    (meshReference (n := 80001) (step := 1) (by decide) d)) atTop
    (𝓝 ((meshReference (n := 80001) (step := 1) (by decide) d)
      (meshLimitPotential (n := 80001) (step := 1) (by decide) d))) :=
  @mesh_radialSelf_limit 80001 1 (by decide) d

private theorem residual_self_limit (s : Shape) (rows : List SpatialLane) :
    Tendsto (fun k => radialSelf (innerRadius k) (remainderCharge s rows)) atTop
      (𝓝 (remainderCharge s rows (residualPotential rows s))) :=
  transport_self_limit (remainderCharge s rows) (meshReference (n := 80001) (step := 1) (by decide) (residualJump rows s.widths))
    (residualPotential rows s) (meshLimitPotential (n := 80001) (step := 1) (by decide) (residualJump rows s.widths))
    rfl rfl (fine_self_limit (residualJump rows s.widths))

private theorem row_self_limit (v : SpatialLane) :
    Tendsto (fun k => radialSelf (innerRadius k) (laneCharge v)) atTop (𝓝 (laneCharge v (lanePotential v))) :=
  transport_self_limit (laneCharge v) (meshReference (n := 641) (step := 125) (by decide) v.jump)
    (lanePotential v) (meshLimitPotential (n := 641) (step := 125) (by decide) v.jump)
    rfl rfl (@mesh_radialSelf_limit 641 125 (by decide) v.jump)

private theorem residual_value_eq (s : Shape) (rows : List SpatialLane) (hw : ∀ w∈s.widths, w≤10000) :
    (fullBandCharge s-∑ j : Fin rows.length, laneCharge (rows.get j)) (residualPotential rows s)=
      remainderCharge s rows (residualPotential rows s) :=
  congrArg (fun Q : ContinuousCharge FrequencyInterval => Q (residualPotential rows s))
    (show (fullBandCharge s-∑ j : Fin rows.length, laneCharge (rows.get j))=remainderCharge s rows from
      (residual_meshReference s rows hw).symm)

theorem referenceInnerTerm_limit (s : Shape) (hw : ∀ w∈s.widths, w≤10000) (hL : 0 < s.totalWidthQ)
    (rows : List SpatialLane) (hn : 0 < rows.length) (a : AnchorPlan) (p : ℤ) :
    Tendsto (fun k => referenceInnerTerm s rows hn a p (innerRadius k)) atTop
      (𝓝 ((s.totalWidthQ : ℝ)*continuousReferenceRate s rows hn a p)) := by
  have H (j : Fin rows.length) := row_self_limit (rows.get j)
  have H₁ := tendsto_finsetSum univ (fun j _ => ((H j).div_const 2).const_sub
    (((s.massList[j.val]?.getD 0 : ℚ) : ℝ)*(((rows.get j).β : ℝ)/100000)))
  have hS := residual_self_limit s rows
  have H₂ := hS.div_const (2*(rows.length : ℝ))
  have H₃ := ((referenceRadialError_limit rows).const_mul (s.totalWidthQ : ℝ)).const_add
    (∑ i ∈ range 80000, cellValue rows hn s.widths a p i)
  have hL' : (s.totalWidthQ : ℝ)≠0 := by exact_mod_cast hL.ne'
  rw [continuousReferenceRate,mul_div_cancel₀ _ hL',residual_value_eq s rows hw]
  simpa only [referenceInnerTerm,referenceRowsTerm,mul_zero,add_zero,mul_div_assoc] using (H₃.add H₁).add H₂

theorem twoStage_upper {ι : Type*} {F : Filter ι} {u : ℕ → ι → ℝ} {v : ℕ → ℝ} {A B ε : ℝ}
    (hu : ∀ k, Tendsto (u k) F (𝓝 (v k))) (hv : Tendsto v atTop (𝓝 A)) (h : A≤B) (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ᶠ i in F, u k i<B+ε := by
  filter_upwards [hv.eventually (gt_mem_nhds (show A<B+ε by linarith))] with k hk
  exact (hu k).eventually (gt_mem_nhds hk)

end PiPolynomialValues
