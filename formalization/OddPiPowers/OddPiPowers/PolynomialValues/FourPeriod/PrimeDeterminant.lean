module

public import OddPiPowers.PolynomialValues.FourPeriod.GaussianContent
public import OddPiPowers.PolynomialValues.FourPeriod.DenominatorWitness

/-! Convert independent local divisibilities of matrix entries into a
single valuation bound for the factorial-normalized polynomial. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

theorem pow_dvd_det_of_entry_loss {R : Type*} [CommRing R] {n : ℕ}
    (p : R) (A : Matrix (Fin n) (Fin n) R) (a b : Fin n → ℕ)
    (h : ∀ i j, p^(a i-b j) ∣ A i j) :
    p^((∑ i, a i)-(∑ j, b j)) ∣ A.det := by
  classical
  rw [Matrix.det_apply']
  apply dvd_sum
  intro σ _
  apply dvd_mul_of_dvd_right
  have he : (∑ i, a i)-(∑ j, b j) ≤ ∑ j, (a (σ j) - b j) := by
    apply Nat.sub_le_iff_le_add.mpr
    rw [← Equiv.sum_comp σ a, ← sum_add_distrib]
    exact sum_le_sum (fun j _ => by omega)
  apply (pow_dvd_pow p he).trans
  rw [← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ (fun j _ => h (σ j) j)

theorem rowFactorial_factorization {n : ℕ} (rows : Fin n → ℤ × ℕ) (p : ℕ) :
    (rowFactorial rows).factorization p = ∑ i, ((rows i).2.factorial).factorization p := by
  exact Nat.factorization_prod_apply (fun i _ => Nat.factorial_ne_zero _)

end PiPolynomialValues.FourPeriod
