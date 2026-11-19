module

public import OddPiPowers.PolynomialValues.FourPeriod.NodeScaling
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Choose.Basic

/-! Divisibility at the origin of the actual Gaussian-integer determinant.
Rows with the same order and residue can only use distinct coefficient
degrees in a nonzero term of the multilinear expansion. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

private theorem choose_two_le_sum (S : Finset ℕ) : S.card.choose 2 ≤ ∑ k ∈ S, k := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hm ih =>
    have ha : a ∉ S := fun ha => (lt_irrefl a) (hm a ha)
    have hs : S.card ≤ a := by
      simpa only [card_range] using card_le_card (show S ⊆ range a from fun k hk => mem_range.mpr (hm k hk))
    rw [card_insert_of_notMem ha, sum_insert ha, Nat.choose_succ_succ, Nat.choose_one_right]
    exact add_le_add hs ih

def rowTag (r : ℤ × ℕ) : ℤ × ℕ := (r.1 % 4, r.2)

def originOrder {n : ℕ} (rows : Fin n → ℤ × ℕ) : ℕ :=
  let tag := rowTag ∘ rows
  ∑ k ∈ univ.image tag, ((univ.filter (fun i => tag i = k)).card).choose 2

private theorem originOrder_le {n : ℕ} (rows : Fin n → ℤ × ℕ) (d : Fin n → ℕ)
    (hd : Function.Injective (fun i => (rowTag (rows i), d i))) :
    originOrder rows ≤ ∑ i, d i := by
  let tag := rowTag ∘ rows
  let F (k : ℤ × ℕ) := univ.filter (fun i => tag i = k)
  have hinj (k) : Set.InjOn d (F k) := by
    intro i hi j hj he
    exact hd (Prod.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) he)
  calc
    originOrder rows ≤ ∑ k ∈ univ.image tag, ∑ i ∈ F k, d i := by
      apply sum_le_sum
      intro k _
      have h := choose_two_le_sum ((F k).image d)
      rwa [card_image_of_injOn (hinj k), sum_image (hinj k)] at h
    _ = _ := sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem tag hi) d

/-- The exponent counts each pair of rows having identical derivative order
and congruent signed nodes. It does not depend on the chosen specialization. -/
theorem originOrder_dvd_rawDeterminant {n : ℕ} (rows cols : Fin n → ℤ × ℕ) :
    (X : GaussianInt[X]) ^ originOrder rows ∣ rawDeterminant rows cols := by
  classical
  let m := (univ : Finset (Fin n)).sup (fun j => (cols j).2) + 1
  have hm (j : Fin n) : (cols j).2 < m :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i : Fin n => (cols i).2) (mem_univ j))
  let a (i : Fin n) (h : Fin m) : GaussianInt[X] := C (((rows i).1 : GaussianInt)^h.val) * X^h.val
  let line (k : ℤ × ℕ) (h : Fin m) (j : Fin n) : GaussianInt[X] :=
    C (originCoefficient k.1 k.2 h.val (cols j).1 (cols j).2)
  let L := (Matrix.detRowAlternating (n := Fin n) (R := GaussianInt[X])).toMultilinearMap
  have hd : rawDeterminant rows cols = L (fun i => ∑ h, a i h • line (rowTag (rows i)) h) := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    simpa only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, a, line, rowTag] using
      rawEntry_expansion (rows i).1 (cols j).1 (rows i).2 (cols j).2 m (hm j)
  rw [hd, L.map_sum]
  apply Finset.dvd_sum
  intro h _
  rw [L.map_smul_univ, smul_eq_mul]
  by_cases hi : Function.Injective (fun i => (rowTag (rows i), (h i).val))
  · have hle := originOrder_le rows (fun i => (h i).val) hi
    apply dvd_mul_of_dvd_left _ _
    apply (pow_dvd_pow (X : GaussianInt[X]) hle).trans
    simp only [a, prod_mul_distrib, prod_pow_eq_pow_sum]
    exact dvd_mul_left _ _
  · obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp hi
    have hk : rowTag (rows i) = rowTag (rows j) := congrArg Prod.fst he
    have hh : h i = h j := Fin.ext (congrArg Prod.snd he)
    have hz : L (fun i => line (rowTag (rows i)) (h i)) = 0 := by
      apply Matrix.det_zero_of_row_eq hne
      rw [hk, hh]
    rw [hz, mul_zero]
    exact dvd_zero _

end PiPolynomialValues.FourPeriod
