module

public import OddPiPowers.PolynomialValues.Numerics.AngleMixture

/-! The angular cells partition the actual probability almost everywhere.
Their rational mixtures give positive weights with total one on both faces. -/

@[expose] public section

namespace PiPolynomialValues

open MeasureTheory Set Filter Real FourPeriod

theorem foldedAngle_positive_ae {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᵐ w ∂poissonLaw r, 0 < foldedAngle w := by
  let f (θ : ℝ) : ℝ := if θ=0 then 1 else 0
  have hm : Measurable f := measurable_const.piecewise (measurableSet_singleton 0) measurable_const
  have hb (θ : ℝ) (_ : θ∈Icc 0 (π/2)) : |f θ|≤1 := by unfold f; split_ifs <;> norm_num
  have hw : ‖(r : ℂ)‖<1 := by simpa [abs_of_pos hr] using hr1
  have H := poissonLaw_fold hr hr1 hm hb
  have ht : (∫ θ in 0..π/2, foldedPoisson r θ*f θ)=0 := by
    rw [intervalIntegral.integral_of_le (by positivity : 0≤π/2)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with θ hθ
    simp [f,ne_of_gt hθ.1]
  rw [ht] at H
  have he := (integral_eq_zero_iff_of_nonneg (fun w : ℂ => show 0≤f (foldedAngle w) by
    unfold f; split_ifs <;> norm_num) (foldedTest_integrable hw hm hb)).mp H
  filter_upwards [he] with w hh
  have hn : foldedAngle w≠0 := fun hz => by simp [f,hz] at hh
  exact lt_of_le_of_ne (foldedAngle_mem w).1 hn.symm

theorem Angular_gates_one_ae {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {es : List ArcRow}
    (h : arcChain 0 1 es=true) :
    ∀ᵐ w ∂poissonLaw r, (es.map fun e => e.gate (foldedAngle w)).sum=1 := by
  filter_upwards [foldedAngle_positive_ae hr hr1] with w hw
  have hh : foldedAngle w∈Ioc 0 (π/2) := ⟨hw,(foldedAngle_mem w).2⟩
  simpa only [arcAngle_zero,arcAngle_one,if_pos hh] using arcChain_gates h (foldedAngle w)

noncomputable def AngleDesign.realMix (D : AngleDesign) (c : AngleCell) (f : AngleLabel → ℝ) :=
  (c.parts.map fun p => (p.2 : ℝ)*f (D.labels[p.1]?.getD default)).sum

noncomputable def AngleDesign.weightAt (D : AngleDesign) (θ : ℝ) (f : AngleLabel → ℝ) :=
  (D.cells.map fun c => c.arc.gate θ*D.realMix c f).sum

theorem AngleDesign.realMix_rat (D : AngleDesign) (c : AngleCell) (f : AngleLabel → ℚ) :
    D.realMix c (fun t => (f t : ℝ))=(D.mix c f : ℝ) := by
  simp [realMix,mix,Rat.cast_list_sum,List.map_map,Function.comp_def]

theorem AngleDesign.weightAt_form (D : AngleDesign) (f : AngleLabel → ℚ) (θ : ℝ) :
    D.weightAt θ (fun t => (f t : ℝ))=(D.form f).field θ := by
  simp [weightAt,realMix_rat,form,ArcForm.field,List.map_map,Function.comp_def,mul_comm]

private theorem map_sum_mono_mem {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ a∈l, f a≤g a) : (l.map f).sum≤(l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem AngleDesign.realMix_mono (D : AngleDesign) (s : Shape) (arcs : List ArcRow) (h : D.valid s arcs=true)
    (c : AngleCell) (hc : c∈D.cells) {f g : AngleLabel → ℝ} (hfg : ∀ t∈D.labels, f t≤g t) :
    D.realMix c f≤D.realMix c g := by
  obtain ⟨_,hparts,_⟩ := of_decide_eq_true h
  obtain ⟨_,hpos⟩ := of_decide_eq_true (List.all_eq_true.mp hparts c hc)
  unfold realMix
  apply map_sum_mono_mem
  intro p hp
  obtain ⟨hi,hw⟩ := of_decide_eq_true (List.all_eq_true.mp hpos p hp)
  rw [List.getElem?_eq_getElem hi,Option.getD_some]
  exact mul_le_mul_of_nonneg_left (hfg _ (List.getElem_mem hi)) (by exact_mod_cast hw)

theorem AngleDesign.weightAt_mono (D : AngleDesign) (s : Shape) (arcs : List ArcRow) (h : D.valid s arcs=true)
    (θ : ℝ) {f g : AngleLabel → ℝ} (hfg : ∀ t∈D.labels, f t≤g t) : D.weightAt θ f≤D.weightAt θ g := by
  unfold weightAt
  apply map_sum_mono_mem
  intro c hc
  apply mul_le_mul_of_nonneg_left (D.realMix_mono s arcs h c hc hfg)
  unfold ArcRow.gate
  split_ifs <;> norm_num

theorem AngleDesign.weightAt_one (D : AngleDesign) (s : Shape) (arcs : List ArcRow) (h : D.valid s arcs=true)
    (θ : ℝ) (hgate : (arcs.map fun e => e.gate θ).sum=1) : D.weightAt θ (fun _ => 1)=1 := by
  obtain ⟨he,hparts,_⟩ := of_decide_eq_true h
  have hm (c : AngleCell) (hc : c∈D.cells) : D.realMix c (fun _ => 1)=1 := by
    have ha := (of_decide_eq_true (List.all_eq_true.mp hparts c hc)).1
    unfold realMix
    simp only [mul_one]
    simpa only [Rat.cast_list_sum,List.map_map,Function.comp_def,Rat.cast_one] using
      congrArg (fun q : ℚ => (q : ℝ)) ha
  rw [← he] at hgate
  calc
    D.weightAt θ (fun _ => 1) = (D.cells.map fun c => c.arc.gate θ).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro c hc
      rw [hm c hc,mul_one]
    _ = 1 := by simpa only [List.map_map,Function.comp_def] using hgate

end PiPolynomialValues
