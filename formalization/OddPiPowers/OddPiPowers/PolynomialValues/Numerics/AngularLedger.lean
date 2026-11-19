module

public import OddPiPowers.PolynomialValues.Analysis.BoundaryHalves

/-! A signed coefficient on each angular cell can be integrated against
the actual boundary law. Directed bounds use the appropriate end of
the mass or sine enclosure even when the coefficient is negative. -/

@[expose] public section

namespace PiPolynomialValues

open MeasureTheory Complex Real Filter

abbrev ArcForm := List (ArcRow × ℚ)

noncomputable def ArcRow.boundaryWeight (e : ArcRow) (z : ℚ) (sine : Bool) : ℝ :=
  if sine then ∫ w : ℂ, e.gate (foldedAngle w)*|w.im| ∂poissonLaw z
  else ∫ w, e.gate (foldedAngle w) ∂poissonLaw z

def ArcRow.weightLo (e : ArcRow) (sine : Bool) : ℚ := if sine then e.sineLo else e.massLo
def ArcRow.weightHi (e : ArcRow) (sine : Bool) : ℚ := if sine then e.sineHi else e.massHi

theorem ArcRow.weight_enclosed (e : ArcRow) (z : ℚ) (sine : Bool) (h : e.passes z=true) :
    (e.weightLo sine : ℝ)≤e.boundaryWeight z sine ∧ e.boundaryWeight z sine≤(e.weightHi sine : ℝ) := by
  cases sine
  · exact (e.boundary_enclosed z h).1
  · exact (e.boundary_enclosed z h).2

def ArcForm.upper (f : ArcForm) (sine : Bool) : ℚ :=
  (f.map fun p => max (p.2*p.1.weightLo sine) (p.2*p.1.weightHi sine)).sum

def ArcForm.lower (f : ArcForm) (sine : Bool) : ℚ :=
  (f.map fun p => min (p.2*p.1.weightLo sine) (p.2*p.1.weightHi sine)).sum

noncomputable def ArcForm.actual (f : ArcForm) (z : ℚ) (sine : Bool) : ℝ :=
  (f.map fun p => (p.2 : ℝ)*p.1.boundaryWeight z sine).sum

theorem ArcForm.enclose (f : ArcForm) (z : ℚ) (sine : Bool) (hp : ∀ p∈f, p.1.passes z=true) :
    (ArcForm.lower f sine : ℝ)≤ArcForm.actual f z sine ∧ ArcForm.actual f z sine≤(ArcForm.upper f sine : ℝ) := by
  induction f with
  | nil => simp [lower,upper,actual]
  | cons p f ih =>
    have H := p.1.weight_enclosed z sine (hp p (by simp))
    have hh := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    let a := (p.2 : ℝ)
    let x := (p.1.weightLo sine : ℝ)
    let y := (p.1.weightHi sine : ℝ)
    let t := p.1.boundaryWeight z sine
    have ht : x≤t ∧ t≤y := H
    have h₁ : min (a*x) (a*y)≤a*t ∧ a*t≤max (a*x) (a*y) := by
      rcases le_total 0 a with ha|ha
      · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left ht.1 ha),
          (mul_le_mul_of_nonneg_left ht.2 ha).trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left ht.2 ha),
          (mul_le_mul_of_nonpos_left ht.1 ha).trans (le_max_left _ _)⟩
    change ((min _ _+ArcForm.lower f sine : ℚ) : ℝ)≤a*t+ArcForm.actual f z sine ∧ a*t+ArcForm.actual f z sine≤((max _ _+ArcForm.upper f sine : ℚ) : ℝ)
    push_cast
    exact ⟨add_le_add h₁.1 hh.1,add_le_add h₁.2 hh.2⟩

noncomputable def ArcForm.field (f : ArcForm) (θ : ℝ) := (f.map fun p => (p.2 : ℝ)*p.1.gate θ).sum

theorem ArcForm.field_measurable (f : ArcForm) : Measurable f.field := by
  induction f with
  | nil => exact measurable_const
  | cons p f ih => exact (measurable_const.mul p.1.gate_measurable).add ih

theorem ArcForm.field_abs (f : ArcForm) (θ : ℝ) : |f.field θ|≤(f.map fun p => |(p.2 : ℝ)|).sum := by
  induction f with
  | nil => simp [field]
  | cons p f ih =>
    change |(p.2 : ℝ)*p.1.gate θ+ArcForm.field f θ|≤|(p.2 : ℝ)|+_
    apply (abs_add_le _ _).trans (add_le_add _ ih)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (p.1.gate_abs_le _)

theorem ArcForm.integral_field (f : ArcForm) (z : ℚ) (hz : ‖((z : ℝ) : ℂ)‖<1) :
    (∫ w, ArcForm.field f (foldedAngle w) ∂poissonLaw z)=ArcForm.actual f z false ∧
    (∫ w : ℂ, ArcForm.field f (foldedAngle w)*|w.im| ∂poissonLaw z)=ArcForm.actual f z true := by
  let μ := poissonLaw (z : ℝ)
  have hunit : ∀ᵐ w ∂μ, ‖|w.im|‖≤1 := (poissonLaw_unit (z : ℝ)).mono (fun w hw => by
    simpa only [Real.norm_eq_abs,abs_abs] using (Complex.abs_im_le_norm w).trans_eq hw)
  have hmeas := Complex.continuous_im.abs.aestronglyMeasurable (μ := μ)
  induction f with
  | nil => simp [field,actual]
  | cons p f ih =>
    have h₁ := foldedTest_integrable hz p.1.gate_measurable (fun θ _ => p.1.gate_abs_le θ)
    have h₂ := foldedTest_integrable hz (ArcForm.field_measurable f) (fun θ _ => ArcForm.field_abs f θ)
    let a := (p.2 : ℝ)
    let g := fun w => p.1.gate (foldedAngle w)
    let h := fun w => ArcForm.field f (foldedAngle w)
    change (∫ w, a*g w+h w ∂μ)=a*(∫ w, g w ∂μ)+ArcForm.actual f z false ∧
      (∫ w : ℂ, (a*g w+h w)*|w.im| ∂μ)=a*(∫ w : ℂ, g w*|w.im| ∂μ)+ArcForm.actual f z true
    constructor
    · rw [integral_add (h₁.const_mul a) h₂,integral_const_mul,← ih.1]
    · simp only [add_mul,mul_assoc]
      rw [integral_add ((h₁.mul_bdd hmeas hunit).const_mul a) (h₂.mul_bdd hmeas hunit),
        integral_const_mul,← ih.2]

end PiPolynomialValues
