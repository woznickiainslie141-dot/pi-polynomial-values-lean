module

public import OddPiPowers.PolynomialValues.FourPeriod.DifferenceExpansion
public import OddPiPowers.PolynomialValues.FourPeriod.PrimeRankBudget

/-! A finite upper bound for each large prime in the actual common
denominator. Any chosen set of tail levels can be used at that prime. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

def primeLevelBudget {n J : ℕ} {U : Fin J → ℕ} (rows : Fin n → ℤ × ℕ)
    (d : Fin n ≃ Column U) (p : ℕ) (H : Finset ℕ) : ℤ :=
  (∑ j, ((d j).1.val : ℤ)) - groupedRankCharge H p rows -
    ∑ j, (levelsBelow H ((d j).1.val + columnOrder (d j)/p) : ℤ)

theorem raw_prime_level_bound {V J n : ℕ} {U : Fin J → ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (node : Fin V → ℤ) (d : Fin n ≃ Column U)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hs : ∀ i, (e i).2.val < p^2) (H : Finset ℕ) :
    let rows := fun i => (node (e i).1,(e i).2.val)
    C ((p^((rowFactorial rows).factorization p-(primeLevelBudget rows d p H).toNat) : ℕ) : GaussianInt) ∣
      rawDeterminant rows (fun j => columnLabel (d j)) := by
  let rows (i : Fin n) := (node (e i).1,(e i).2.val)
  let F := rowFactorial rows
  let E := (primeLevelBudget rows d p H).toNat
  apply raw_dvd_of_difference_matchings e node d 0 p (F.factorization p-E) hp hp2 hs
  intro h hi θ hk
  let a (j : Fin n) := (e (θ j)).2.val/p
  let b (j : Fin n) := columnOrder (d j)/p
  let layer (j : Fin n) := (d j).1.val
  let loss (j : Fin n) := min (layer j-h (θ j)) (a j-b j)
  have supp (j : Fin n) : columnOrder (d j) ≤ (e (θ j)).2.val ∧ h (θ j) ≤ layer j :=
    differencedKernel_support (hk j)
  have htot : F.factorization p = ∑ j, a j := by
    rw [show F.factorization p = ∑ i, (e i).2.val.factorial.factorization p from rowFactorial_factorization rows p]
    calc
      _ = ∑ i, (e i).2.val/p := sum_congr rfl (fun i _ => factorial_large _ _ hp (hs i))
      _ = _ := (Equiv.sum_comp θ (fun i => (e i).2.val/p)).symm
  have hsplit : (∑ j, a j) = (∑ j, (a j-loss j)) + ∑ j, loss j := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun j _ => (Nat.sub_add_cancel ((min_le_right _ _).trans (Nat.sub_le _ _))).symm)
  have hr : groupedRankCharge H p rows ≤ ∑ j, primeRankCharge H (a j) (h (θ j)) :=
    (groupedRankCharge_le H p rows h hi).trans_eq
      (Equiv.sum_comp θ (fun i => primeRankCharge H ((rows i).2/p) (h i))).symm
  have hlocal (j) : (loss j : ℤ) + primeRankCharge H (a j) (h (θ j)) + levelsBelow H (layer j+b j) ≤ layer j :=
    matched_level_charge H (a j) (b j) (layer j) (h (θ j)) (Nat.div_le_div_right (supp j).1) (supp j).2
  have hcost : ∑ j, loss j ≤ E := by
    have hh := sum_le_sum (s := univ) (fun j _ => hlocal j)
    rw [sum_add_distrib,sum_add_distrib,← Nat.cast_sum] at hh
    change (∑ j, loss j) ≤ ((∑ j, (layer j : ℤ)) - groupedRankCharge H p rows -
      ∑ j, (levelsBelow H (layer j+b j) : ℤ)).toNat
    omega
  change F.factorization p-E ≤ ∑ j, (a j-loss j)
  rw [htot,hsplit]
  omega

theorem quotient_prime_level_bound {V J n : ℕ} {U : Fin J → ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (node : Fin V → ℤ) (d : Fin n ≃ Column U)
    (q : GaussianInt[X]) (k p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : ∀ i, (e i).2.val < p^2)
    (hd : rawDeterminant (fun i => (node (e i).1,(e i).2.val)) (fun j => columnLabel (d j)) = X^k*q)
    (H : Finset ℕ) :
    let rows := fun i => (node (e i).1,(e i).2.val)
    (commonDenominator (rowFactorial rows) q).factorization p ≤ (primeLevelBudget rows d p H).toNat := by
  let rows := fun i => (node (e i).1,(e i).2.val)
  apply commonDenominator_prime_bound hp (rowFactorial_pos rows).ne'
  apply (C_dvd_strip_origin _ k q).mp
  rw [← hd]
  exact raw_prime_level_bound e node d p hp hp2 hs H

theorem primeLevelBudget_empty {n J : ℕ} {U : Fin J → ℕ} (rows : Fin n → ℤ × ℕ)
    (d : Fin n ≃ Column U) (p : ℕ) : primeLevelBudget rows d p ∅ =
      (∑ j, ((d j).1.val : ℤ)) - originOrder rows := by
  simp [primeLevelBudget,groupedRankCharge_empty,levelsBelow]

end PiPolynomialValues.FourPeriod
