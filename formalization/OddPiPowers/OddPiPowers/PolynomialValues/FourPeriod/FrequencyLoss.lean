module

public import OddPiPowers.PolynomialValues.FourPeriod.MonicRows
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Monic rows with prescribed frequency zeros give an upper degree bound
for one and the same integral determinant, including signed row costs. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

private theorem det_degree_signed {n : ℕ} (A : Matrix (Fin n) (Fin n) GaussianInt[X])
    (a b : Fin n → ℤ)
    (h : ∀ i j, A i j ≠ 0 → ((A i j).natDegree : ℤ) + a i ≤ b j)
    (hn : A.det ≠ 0) : (A.det.natDegree : ℤ) + ∑ i, a i ≤ ∑ j, b j := by
  classical
  let d := A.det.natDegree
  let T (σ : Equiv.Perm (Fin n)) := ∏ i, A (σ i) i
  have hd : A.det.coeff d ≠ 0 := leadingCoeff_ne_zero.mpr hn
  obtain ⟨σ,hσ⟩ : ∃ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ) • T σ).coeff d ≠ 0 := by
    by_contra! hall
    apply hd
    calc
      A.det.coeff d = (∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ • T τ)).coeff d :=
        congrArg (fun p : GaussianInt[X] => p.coeff d) (Matrix.det_apply A)
      _ = 0 := by rw [finsetSum_coeff]; exact sum_eq_zero (fun τ _ => hall τ)
  have ht : T σ ≠ 0 := by intro hz; simp [hz] at hσ
  have hprod : d ≤ ∑ i, (A (σ i) i).natDegree :=
    (le_natDegree_of_ne_zero hσ).trans ((natDegree_smul_le _ _).trans (natDegree_prod_le _ _))
  have hsum := sum_le_sum (s := univ) (fun i _ => h (σ i) i (prod_ne_zero_iff.mp ht i (mem_univ _)))
  rw [sum_add_distrib, Equiv.sum_comp σ a] at hsum
  have hc : (d : ℤ) ≤ ∑ i, ((A (σ i) i).natDegree : ℤ) := by exact_mod_cast hprod
  exact (add_le_add hc le_rfl).trans hsum

noncomputable def frequencyRow (S : Finset ℤ) (m : ℤ → ℕ) (σ : ℕ) : GaussianInt[X] :=
  X ^ (σ - ∑ t ∈ S, m t) * ∏ t ∈ S, (X - C (t : GaussianInt)) ^ m t

theorem frequencyRow_monic (S : Finset ℤ) (m : ℤ → ℕ) (σ : ℕ) :
    (frequencyRow S m σ).Monic :=
  (monic_X.pow _).mul (monic_prod_of_monic S _ (fun t _ => (monic_X_sub_C _).pow _))

theorem frequencyRow_degree (S : Finset ℤ) (m : ℤ → ℕ) (σ : ℕ) (hm : ∑ t ∈ S, m t ≤ σ) :
    (frequencyRow S m σ).natDegree = σ := by
  unfold frequencyRow
  rw [natDegree_mul (monic_X.pow _).ne_zero
    (monic_prod_of_monic S _ (fun t _ => (monic_X_sub_C _).pow _)).ne_zero,
    natDegree_X_pow, natDegree_prod_of_monic _ _ (fun t _ => (monic_X_sub_C _).pow _)]
  simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using Nat.sub_add_cancel hm

theorem frequencyRow_root (S : Finset ℤ) (m : ℤ → ℕ) (σ : ℕ) {t : ℤ} (ht : t ∈ S) :
    (X - C (t : GaussianInt)) ^ m t ∣ frequencyRow S m σ :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun s : ℤ => (X - C (s : GaussianInt)) ^ m s) ht) _

theorem raw_degree_frequency_loss {n V : ℕ} {count : Fin V → ℕ} (e : Fin n ≃ RowCandidates count)
    (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ) (S : Finset ℤ) (hs : ∀ j, (cols j).1 ∈ S)
    (mult : Fin n → ℤ → ℕ) (a b : Fin n → ℤ)
    (hm : ∀ i, ∑ t ∈ S, mult i t ≤ (e i).2.val)
    (hloss : ∀ i j, a i + b j ≤ (mult i (cols j).1 : ℤ))
    (hn : rawDeterminant (fun i => (node (e i).1, (e i).2.val)) cols ≠ 0) :
    ((rawDeterminant (fun i => (node (e i).1, (e i).2.val)) cols).natDegree : ℤ) +
      (∑ i, a i) + (∑ j, b j) ≤ ∑ j, ((cols j).2 : ℤ) := by
  let p (i) := frequencyRow S (mult i) (e i).2.val
  let A := rowPolynomialMatrix e node cols p
  have he (i : Fin n) : (p i).natDegree = (e i).2.val := frequencyRow_degree _ _ _ (hm i)
  have heq : A.det = rawDeterminant (fun i => (node (e i).1, (e i).2.val)) cols :=
    rowPolynomialMatrix_det e node cols p (fun i => (he i).le) (fun i => by
      rw [← he i, coeff_natDegree]
      exact frequencyRow_monic _ _ _)
  have hb (i j) (hh : A i j ≠ 0) : ((A i j).natDegree : ℤ) + a i ≤ ((cols j).2 : ℤ) - b j := by
    have hex := entryWithRow_degree_loss (node (e i).1) (cols j).1 (cols j).2 (mult i (cols j).1)
      (p i) (frequencyRow_root _ _ _ (hs j)) hh
    have hc : ((A i j).natDegree : ℤ) + (mult i (cols j).1 : ℤ) ≤ ((cols j).2 : ℤ) := by
      exact_mod_cast hex
    have := hloss i j
    omega
  have hd := det_degree_signed A a (fun j => ((cols j).2 : ℤ)-b j) hb (heq ▸ hn)
  rw [heq, sum_sub_distrib] at hd
  omega

end PiPolynomialValues.FourPeriod
