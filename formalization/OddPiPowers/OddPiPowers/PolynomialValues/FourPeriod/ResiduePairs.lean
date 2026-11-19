module

public import OddPiPowers.PolynomialValues.FourPeriod.VandermondeCollisions
public import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

/-! The marked factors of the actual frequency Vandermonde, counted once
for each unordered pair in each residue class. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

def residueTag {p : ℕ} (hp : 0 < p) (x : ℤ) : Fin p :=
  ⟨(x % (p : ℤ)).toNat, by
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    have h := Int.emod_lt_of_pos x hp'
    omega⟩

theorem residueTag_eq_iff {p : ℕ} (hp : 0 < p) (x y : ℤ) :
    residueTag hp x = residueTag hp y ↔ x ≡ y [ZMOD p] := by
  rw [Fin.ext_iff]
  change (x % (p : ℤ)).toNat = (y % (p : ℤ)).toNat ↔ x % (p : ℤ) = y % (p : ℤ)
  have hp' : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne'
  have hx := Int.emod_nonneg x hp'
  have hy := Int.emod_nonneg y hp'
  omega

def residueMultiplicity {n p : ℕ} (hp : 0 < p) (x : Fin n → ℤ) (r : Fin p) : ℕ :=
  (univ.filter (fun i => residueTag hp (x i) = r)).card

theorem sum_residueMultiplicity {n p : ℕ} (hp : 0 < p) (x : Fin n → ℤ) :
    (∑ r : Fin p, residueMultiplicity hp x r) = n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
    (t := univ) (f := fun i => residueTag hp (x i)) (fun _ _ => mem_univ _)
  simpa only [residueMultiplicity, card_univ, Fintype.card_fin] using h.symm

theorem collidingPairs_eq_sum_choose {n p : ℕ} (hp : 0 < p) (x : Fin n → ℤ) :
    collidingPairs p x = ∑ r : Fin p, (residueMultiplicity hp x r).choose 2 := by
  let tag (i : Fin n) := residueTag hp (x i)
  let T := (frequencyPairs n).filter (fun e => tag e.1 = tag e.2)
  let F (r : Fin p) := univ.filter (fun i => tag i = r)
  have hT : collidingPairs p x = T.card := by simp only [T, tag, residueTag_eq_iff, collidingPairs]
  have hf (r : Fin p) : T.filter (fun e => tag e.1 = r) =
      (F r ×ˢ F r).filter (fun e => e.1 < e.2) := by
    ext e
    simp only [T, F, frequencyPairs, mem_filter, mem_product, mem_univ, true_and]
    grind
  rw [hT, Finset.card_eq_sum_card_fiberwise (s := T) (t := univ) (f := fun e => tag e.1)
    (fun _ _ => mem_univ _)]
  apply sum_congr rfl
  intro r _
  rw [hf, Finset.card_product_filter_lt]
  rfl

private theorem twice_choose_two (n : ℕ) : 2*(n.choose 2 : ℤ) = (n : ℤ)*((n : ℤ)-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (n+1).choose 2 = n + n.choose 2 := by simpa using Nat.choose_succ_succ n 1
    rw [h, Nat.cast_add, Nat.cast_succ]
    nlinarith only [ih]

theorem twice_collidingPairs {n p : ℕ} (hp : 0 < p) (x : Fin n → ℤ) :
    2*(collidingPairs p x : ℤ) =
      ∑ r : Fin p, (residueMultiplicity hp x r : ℤ)*((residueMultiplicity hp x r : ℤ)-1) := by
  rw [collidingPairs_eq_sum_choose hp, Nat.cast_sum, Finset.mul_sum]
  exact sum_congr rfl (fun r _ => twice_choose_two _)

end PiPolynomialValues.FourPeriod
