module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Divisibility.Basic

/-! A derivative can remove at most one marked factor of a prime from
the evaluated product. This proof also allows coincident frequencies. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

variable {ι β A R : Type*} [CommRing A] [CommRing R]

def iterPartials (D : ι → A →+ A) : List ι → A →+ A
  | [] => AddMonoidHom.id A
  | i :: ds => (iterPartials D ds).comp (D i)

def derivativeDivisibility (D : ι → A →+ A) (v : A →+* R) (q : R) (k : ℕ) (f : A) : Prop :=
  ∀ ds : List ι, q ^ (k-ds.length) ∣ v (iterPartials D ds f)

private theorem after_one_derivative {D : ι → A →+ A} {v : A →+* R} {q : R}
    {k : ℕ} {f : A} (hf : derivativeDivisibility D v q k f) (i : ι) :
    derivativeDivisibility D v q (k-1) (D i f) := by
  intro ds
  have e : k - (i::ds).length = k-1-ds.length := by simp only [List.length_cons]; omega
  simpa only [e, iterPartials, AddMonoidHom.comp_apply] using hf (i::ds)

theorem derivativeDivisibility_mul (D : ι → A →+ A)
    (hleib : ∀ i f g, D i (f*g) = D i f * g + f * D i g)
    (v : A →+* R) (q : R) (k h : ℕ) (f g : A)
    (hf : derivativeDivisibility D v q k f) (hg : derivativeDivisibility D v q h g) :
    derivativeDivisibility D v q (k+h) (f*g) := by
  intro ds
  induction ds generalizing k h f g with
  | nil =>
    simpa [iterPartials, pow_add] using mul_dvd_mul (hf []) (hg [])
  | cons i ds ih =>
    have h₁ := ih (k := k-1) (h := h) (f := D i f) (g := g) (after_one_derivative hf i) hg
    have h₂ := ih (k := k) (h := h-1) (f := f) (g := D i g) hf (after_one_derivative hg i)
    change q ^ (k+h-(ds.length+1)) ∣ v (iterPartials D ds (D i (f*g)))
    simp only [hleib, map_add]
    exact dvd_add ((pow_dvd_pow q (by omega : k+h-(ds.length+1) ≤ k-1+h-ds.length)).trans h₁)
      ((pow_dvd_pow q (by omega : k+h-(ds.length+1) ≤ k+(h-1)-ds.length)).trans h₂)

private theorem derivativeDivisibility_prod (D : ι → A →+ A)
    (hleib : ∀ i f g, D i (f*g) = D i f * g + f * D i g)
    (v : A →+* R) (q : R) (S : Finset β) (w : β → ℕ) (f : β → A)
    (h : ∀ i ∈ S, derivativeDivisibility D v q (w i) (f i)) :
    derivativeDivisibility D v q (∑ i ∈ S, w i) (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro ds; simp
  | @insert b S hb ih =>
    rw [Finset.sum_insert hb, Finset.prod_insert hb]
    exact derivativeDivisibility_mul D hleib v q _ _ _ _ (h b (by simp))
      (ih (fun a ha => h a (Finset.mem_insert_of_mem ha)))

theorem differentiated_product_dvd (D : ι → A →+ A)
    (hleib : ∀ i f g, D i (f*g) = D i f * g + f * D i g)
    (v : A →+* R) (q : R) (S : Finset β) (f : β → A)
    (mark : β → Prop) [DecidablePred mark] (hv : ∀ i ∈ S, mark i → q ∣ v (f i)) (ds : List ι) :
    q ^ ((S.filter mark).card - ds.length) ∣ v (iterPartials D ds (∏ i ∈ S, f i)) := by
  have h (i : β) (hi : i ∈ S) : derivativeDivisibility D v q (if mark i then 1 else 0) (f i) := by
    intro xs
    by_cases hb : mark i
    · cases xs with
      | nil => simpa [hb, iterPartials] using hv i hi hb
      | cons a xs => simp [hb]
    · simp [hb]
  simpa [Finset.sum_boole] using
    derivativeDivisibility_prod D hleib v q S (fun i => if mark i then 1 else 0) f h ds

end PiPolynomialValues.FourPeriod
