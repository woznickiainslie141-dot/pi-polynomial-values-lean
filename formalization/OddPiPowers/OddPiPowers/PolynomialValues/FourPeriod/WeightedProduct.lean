module

public import OddPiPowers.PolynomialValues.FourPeriod.DifferentiatedProduct
public import Mathlib.Algebra.Polynomial.Derivative

/-! Local divisibility of differentiated products when a derivative may
remove at most L tracked powers of the prime from its chosen factor. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

variable {ι α A R : Type*} [CommRing A] [CommRing R]

private def WeightedDiv (D : ι → A →+ A) (v : A →+* R) (p : R) (L k : ℕ) (f : A) : Prop :=
  ∀ ds, p^(k-L*(ds : List ι).length) ∣ v (iterPartials D ds f)

private theorem weighted_step {D : ι → A →+ A} {v : A →+* R} {p : R} {L k : ℕ}
    {f : A} (hf : WeightedDiv D v p L k f) (i : ι) : WeightedDiv D v p L (k-L) (D i f) := by
  intro ds
  have h := hf (i::ds)
  simp only [iterPartials,AddMonoidHom.comp_apply,List.length_cons,Nat.mul_succ] at h
  have e : k-(L*ds.length+L) = k-L-L*ds.length := by omega
  exact e ▸ h

private theorem weighted_mul (D : ι → A →+ A) (v : A →+* R) (p : R) (L : ℕ)
    (hD : ∀ i f g, D i (f*g) = D i f*g+f*D i g) (a b : ℕ) (f g : A)
    (hf : WeightedDiv D v p L a f) (hg : WeightedDiv D v p L b g) :
    WeightedDiv D v p L (a+b) (f*g) := by
  intro ds
  induction ds generalizing a b f g with
  | nil => simpa [iterPartials,pow_add] using mul_dvd_mul (hf []) (hg [])
  | cons i ds ih =>
    have h₁ := ih (a := a-L) (b := b) (f := D i f) (g := g) (weighted_step hf i) hg
    have h₂ := ih (a := a) (b := b-L) (f := f) (g := D i g) hf (weighted_step hg i)
    simp only [iterPartials,AddMonoidHom.comp_apply,List.length_cons,Nat.mul_succ,hD,map_add]
    apply dvd_add
    · exact (pow_dvd_pow p (by omega : a+b-(L*ds.length+L) ≤ a-L+b-L*ds.length)).trans h₁
    · exact (pow_dvd_pow p (by omega : a+b-(L*ds.length+L) ≤ a+(b-L)-L*ds.length)).trans h₂

theorem weighted_differentiated_product (D : ι → A →+ A) (v : A →+* R) (p : R) (L : ℕ)
    (hD : ∀ i f g, D i (f*g) = D i f*g+f*D i g) (S : Finset α) (w : α → ℕ) (f : α → A)
    (hw : ∀ i ∈ S, w i ≤ L) (hf : ∀ i ∈ S, p^(w i) ∣ v (f i)) (ds : List ι) :
    p^((∑ i ∈ S, w i)-L*ds.length) ∣ v (iterPartials D ds (∏ i ∈ S, f i)) := by
  classical
  suffices h : WeightedDiv D v p L (∑ i ∈ S, w i) (∏ i ∈ S, f i) from h ds
  induction S using Finset.induction_on with
  | empty => intro xs; simp
  | @insert i S hi ih =>
    rw [sum_insert hi,prod_insert hi]
    apply weighted_mul D v p L hD
    · intro xs
      cases xs with
      | nil => simpa [iterPartials] using hf i (by simp)
      | cons a xs =>
        have hi' := hw i (mem_insert_self _ _)
        have hz : w i - L*(a::xs).length = 0 := by simp only [List.length_cons,Nat.mul_succ]; omega
        rw [hz,pow_zero]
        exact one_dvd _
    · exact ih (fun j hj => hw j (mem_insert_of_mem hj)) (fun j hj => hf j (mem_insert_of_mem hj))

private theorem iter_univariate (f : ℤ[X]) (d : ℕ) :
    iterPartials (fun _ : Unit => derivative.toAddMonoidHom) (List.replicate d ()) f =
      (derivative^[d]) f := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply]
    exact ih f.derivative

theorem weighted_integer_poly_product {β : Type*} (S : Finset β) (f : β → ℤ[X]) (w : β → ℕ)
    (p x : ℤ) (L d : ℕ) (hw : ∀ i ∈ S, w i ≤ L) (hf : ∀ i ∈ S, p^(w i) ∣ (f i).eval x) :
    p^((∑ i ∈ S, w i)-L*d) ∣ ((derivative^[d]) (∏ i ∈ S, f i)).eval x := by
  have h := weighted_differentiated_product (fun _ : Unit => derivative.toAddMonoidHom)
    (evalRingHom x) p L (fun _ f g => derivative_mul) S w f hw hf (List.replicate d ())
  simpa only [List.length_replicate,iter_univariate,coe_evalRingHom] using h

end PiPolynomialValues.FourPeriod
