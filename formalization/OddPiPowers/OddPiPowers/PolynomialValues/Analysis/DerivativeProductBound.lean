module

public import OddPiPowers.PolynomialValues.FourPeriod.DifferentiatedProduct
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Bounds for all iterated coordinate derivatives of a finite product.
The derivative loss grows polynomially per derivative in the block size. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

variable {ι β A : Type*} [CommRing A]

def PartialMajorant (D : ι → A →+ A) (v : A →+* ℂ) (a c : ℝ) (f : A) : Prop :=
  ∀ ds : List ι, ‖v (iterPartials D ds f)‖ ≤ a*c^ds.length

theorem PartialMajorant.derivative {D : ι → A →+ A} {v : A →+* ℂ} {a c : ℝ} {f : A}
    (h : PartialMajorant D v a c f) (i : ι) : PartialMajorant D v (a*c) c (D i f) := by
  intro ds
  have hh := h (i::ds)
  simpa only [iterPartials,AddMonoidHom.comp_apply,List.length_cons,pow_succ',mul_assoc] using hh

theorem PartialMajorant.mul (D : ι → A →+ A) (v : A →+* ℂ)
    (hleib : ∀ i f g, D i (f*g) = D i f*g + f*D i g)
    {a b c d : ℝ} {f g : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hf : PartialMajorant D v a c f) (hg : PartialMajorant D v b d g) :
    PartialMajorant D v (a*b) (c+d) (f*g) := by
  intro ds
  induction ds generalizing a b f g with
  | nil =>
    have h₁ : ‖v f‖ ≤ a := by simpa [iterPartials] using hf []
    have h₂ : ‖v g‖ ≤ b := by simpa [iterPartials] using hg []
    simpa [iterPartials] using mul_le_mul h₁ h₂ (norm_nonneg _) ha
  | cons i ds ih =>
    have h₁ := ih (mul_nonneg ha hc) hb (hf.derivative i) hg
    have h₂ := ih ha (mul_nonneg hb hd) hf (hg.derivative i)
    change ‖v (iterPartials D ds (D i (f*g)))‖ ≤ _
    rw [hleib,map_add,map_add]
    apply (norm_add_le _ _).trans
    apply (add_le_add h₁ h₂).trans_eq
    rw [List.length_cons,pow_succ]
    ring

theorem partialMajorant_prod (D : ι → A →+ A) (v : A →+* ℂ)
    (hone : ∀ i, D i 1 = 0) (hleib : ∀ i f g, D i (f*g) = D i f*g + f*D i g)
    (S : Finset β) (a c : β → ℝ) (f : β → A)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hf : ∀ i ∈ S, PartialMajorant D v (a i) (c i) (f i)) :
    PartialMajorant D v (∏ i ∈ S, a i) (∑ i ∈ S, c i) (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro ds
    cases ds with
    | nil => simp [iterPartials]
    | cons i ds => simp [iterPartials,hone]
  | @insert k S hk ih =>
    rw [prod_insert hk,sum_insert hk,prod_insert hk]
    have hS {i} (h : i ∈ S) : i ∈ insert k S := mem_insert_of_mem h
    exact PartialMajorant.mul D v hleib (ha k (by simp)) (prod_nonneg (fun i hi => ha i (hS hi)))
      (hc k (by simp)) (sum_nonneg (fun i hi => hc i (hS hi))) (hf k (by simp))
      (ih (fun i hi => ha i (hS hi)) (fun i hi => hc i (hS hi)) (fun i hi => hf i (hS hi)))

end PiPolynomialValues.FourPeriod
