module

public import OddPiPowers.PolynomialValues.FourPeriod.PrefixBasis
public import OddPiPowers.PolynomialValues.FourPeriod.Normalization
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Extract one square Gaussian-integer polynomial minor from the row scan.
The two equivalences enumerate each retained prefix row and each column once. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

theorem component_prefix_deficit {V : ℕ} (count m : Fin V → ℕ) (hle : ∀ v, m v ≤ count v) (v : Fin V) :
    count v-m v ≤ (∑ w, count w)-(∑ w, m w) := by
  have hsum : (∑ w, (count w - m w)) + (∑ w, m w) = ∑ w, count w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => Nat.sub_add_cancel (hle w))
  have h := Finset.single_le_sum (f := fun w => count w-m w) (s := Finset.univ)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ v)
  omega

def HasPrefixMinor {κ : Type*} [Fintype κ] {V : ℕ} (count : Fin V → ℕ) (node : Fin V → ℤ)
    (cols : κ → ℤ × ℕ) (y : ℂ) : Prop :=
  ∃ m : Fin V → ℕ, (∀ v, m v ≤ count v) ∧ (∑ v, m v) = Fintype.card κ ∧
    (∀ v, count v-m v ≤ (∑ w, count w)-Fintype.card κ) ∧
    ∃ (er : Fin (Fintype.card κ) ≃ RowCandidates m) (ec : Fin (Fintype.card κ) ≃ κ),
      (rawDeterminant (fun i => (node (er i).1,(er i).2.val)) (fun j => cols (ec j))).eval₂
        GaussianInt.toComplex y ≠ 0

theorem prefixMinor_of_candidate_kernel {κ : Type*} [Fintype κ] {V : ℕ}
    (count : Fin V → ℕ) (H : ℕ) (hH : ∀ v, count v ≤ H) (node : Fin V → ℤ)
    (cols : κ → ℤ × ℕ) (pred : κ → κ)
    (hp : ∀ c j, (cols c).2 = j+1 → cols (pred c) = ((cols c).1,j))
    (y : ℂ) (hk : ∀ a : κ → ℂ, (∀ v, ∀ σ < count v,
      ∑ c, a c*normalizedEntry (node v) (cols c).1 σ (cols c).2 y = 0) → a = 0) :
    HasPrefixMinor count node cols y := by
  classical
  let row (v : Fin V) (k : ℕ) := specializedRow cols (node v) k y
  let delay (v : Fin V) := H-count v
  let m := prefixSize count delay row
  let T := frequencyShift cols pred
  have ht (v : Fin V) (k : ℕ) : T (row v k) = row v (k+1) :=
    frequencyShift_row cols pred hp (node v) k y
  have hraw (a : κ → ℂ) (ha : ∀ c : RowCandidates count, ∑ x, a x*row c.1 c.2.val x = 0) :
      a = 0 := by
    apply hk
    intro v σ hσ
    have hf : (σ.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    apply (mul_eq_zero.mp (show (σ.factorial : ℂ)*
      (∑ c, a c*normalizedEntry (node v) (cols c).1 σ (cols c).2 y) = 0 from ?_)).resolve_left hf
    calc
      _ = ∑ c, a c*row v σ c := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        change _ = a c*(rawEntry (node v) (cols c).1 σ (cols c).2).eval₂ GaussianInt.toComplex y
        rw [rawEntry_eq_factorial_mul]
        ring
      _ = 0 := ha ⟨v,σ,hσ⟩
  have hm := prefixSize_sum count H hH row hraw T ht
  have hle := prefixSize_le count delay row
  refine ⟨m,hle,hm,fun v => ?_,?_⟩
  · simpa only [← hm] using component_prefix_deficit count m hle v
  let sel := chosenCandidates count delay row
  let E := chosenPrefixEquiv count delay row T ht
  have hcard : Fintype.card ↥sel = Fintype.card κ := by
    have h := Module.finrank_eq_card_basis (prefixRowBasis count H hH row hraw)
    rwa [Module.finrank_fintype_fun_eq_card, eq_comm] at h
  let e : Fin (Fintype.card κ) ≃ ↥sel := (Fintype.equivFinOfCardEq hcard).symm
  let d : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let M : Matrix (Fin (Fintype.card κ)) (Fin (Fintype.card κ)) ℂ :=
    Matrix.of (fun i j => row (e i).val.1 (e i).val.2.val (d j))
  have hi := (chosenCandidates_independent count delay row).comp e e.injective
  have hM : LinearIndependent ℂ M.row := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hz i
    apply Fintype.linearIndependent_iff.mp hi g _ i
    funext c
    have hh := congrFun hz (d.symm c)
    simpa only [M,Matrix.row,Matrix.of_apply,Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,
      Function.comp_apply,d.apply_symm_apply] using hh
  refine ⟨e.trans E,d,?_⟩
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp hM)).ne_zero
  have he : (rawDeterminant (fun i => (node (E (e i)).1,(E (e i)).2.val))
      (fun j => cols (d j))).eval₂ GaussianInt.toComplex y = M.det := by
    change (eval₂RingHom GaussianInt.toComplex y) (Matrix.of fun i j =>
      rawEntry (node (E (e i)).1) (cols (d j)).1 (E (e i)).2.val (cols (d j)).2).det = _
    rw [RingHom.map_det]
    apply congrArg Matrix.det
    ext i j
    rfl
  exact fun hc => hdet (he.symm.trans hc)

end PiPolynomialValues.FourPeriod
