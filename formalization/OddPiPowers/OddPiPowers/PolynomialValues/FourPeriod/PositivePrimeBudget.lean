module

public import OddPiPowers.PolynomialValues.FourPeriod.SelectedPolynomial

/-! Nonvanishing forces an actual nonzero matching in the differenced
matrix. Hence the signed prime budget is nonnegative at each prime. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

theorem exists_difference_matching {V J n : ℕ} {U : Fin J → ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (node : Fin V → ℤ) (d : Fin n ≃ Column U)
    (a : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hs : ∀ i, (e i).2.val < p^2)
    (hn : rawDeterminant (fun i => (node (e i).1,(e i).2.val)) (fun j => columnLabel (d j)) ≠ 0) :
    ∃ (h : Fin n → ℕ), Function.Injective (fun i => (rowTag (node (e i).1,(e i).2.val),h i)) ∧
      ∃ θ : Equiv.Perm (Fin n), ∀ j,
        columnKernel a (rowTag (node (e (θ j)).1,(e (θ j)).2.val)) (h (θ j)) (d j) ≠ 0 := by
  classical
  let Q := rawDeterminant (fun i => (node (e i).1,(e i).2.val)) (fun j => columnLabel (d j))
  let c := gaussianContent Q
  have hc : c ≠ 0 := by
    intro hz
    have hd := (dvd_gaussianContent_iff 0 Q).mp (show 0 ∣ c by rw [hz])
    exact hn (by simpa using hd)
  by_contra hnone
  let M := c.factorization p + 1
  have hd : C ((p^M : ℕ) : GaussianInt) ∣ Q := by
    apply raw_dvd_of_difference_matchings e node d a p M hp hp2 hs
    intro h hi θ hθ
    exact False.elim (hnone ⟨h,hi,θ,hθ⟩)
  have hh := (hp.pow_dvd_iff_le_factorization hc).mp ((dvd_gaussianContent_iff _ Q).mpr hd)
  exact (Nat.not_succ_le_self _) hh

theorem SelectedPolynomial.level_cost_int {s : Shape} {g : List (List ℤ)} {t a b : ℕ} {y : ℂ}
    (w : SelectedPolynomial s g t y a b) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : ∀ v, w.count v ≤ p^2) (H : Finset ℕ) :
    (w.denominator.factorization p : ℤ) ≤ primeLevelBudget w.rows w.colIndex p H := by
  let e := w.rowIndex
  let d := w.colIndex
  let node := scannedNode g
  have hq : w.quotient ≠ 0 := by intro h; exact w.quotient_eval_ne (by simp [h])
  have hn : rawDeterminant (fun i => (node (e i).1,(e i).2.val)) (fun j => columnLabel (d j)) ≠ 0 := by
    rw [w.raw_eq]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) hq
  obtain ⟨h,hi,θ,hθ⟩ := exists_difference_matching e node d 0 p hp hp2
    (fun i => (e i).2.isLt.trans_le (hm _)) hn
  let A (j : Fin _) := (e (θ j)).2.val/p
  let B (j : Fin _) := columnOrder (d j)/p
  let lay (j : Fin _) := (d j).1.val
  have hr : groupedRankCharge H p w.rows ≤ ∑ j, primeRankCharge H (A j) (h (θ j)) :=
    (groupedRankCharge_le H p w.rows h hi).trans_eq
      (Equiv.sum_comp θ (fun i => primeRankCharge H ((w.rows i).2/p) (h i))).symm
  have hl (j) : primeRankCharge H (A j) (h (θ j)) + levelsBelow H (lay j+B j) ≤ (lay j : ℤ) := by
    have hs := differencedKernel_support (hθ j)
    have hh := matched_level_charge H (A j) (B j) (lay j) (h (θ j)) (Nat.div_le_div_right hs.1) hs.2
    omega
  have hh := sum_le_sum (s := univ) (fun j _ => hl j)
  rw [sum_add_distrib] at hh
  have hz : 0 ≤ primeLevelBudget w.rows w.colIndex p H := by
    change 0 ≤ ∑ j, (lay j : ℤ) - groupedRankCharge H p w.rows - ∑ j, (levelsBelow H (lay j+B j) : ℤ)
    omega
  have hh' := w.level_cost p hp hp2 hm H
  omega

end PiPolynomialValues.FourPeriod
