module

public import OddPiPowers.PolynomialValues.FourPeriod.GaussianContent
public import OddPiPowers.PolynomialValues.FourPeriod.Normalization
import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! One positive rational-integer denominator and a Gaussian-integer
quotient polynomial representing the factorial-normalized determinant. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

def rowFactorial {n : ℕ} (rows : Fin n → ℤ × ℕ) : ℕ := ∏ i, (rows i).2.factorial

theorem rowFactorial_pos {n : ℕ} (rows : Fin n → ℤ × ℕ) : 0 < rowFactorial rows :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

noncomputable def normalizedDetValue {n : ℕ} (rows cols : Fin n → ℤ × ℕ) (x : ℂ) : ℂ :=
  (Matrix.of fun i j => normalizedEntry (rows i).1 (cols j).1 (rows i).2 (cols j).2 x).det

theorem exists_cleared_quotient {n k : ℕ} (rows cols : Fin n → ℤ × ℕ) (y : ℂ)
    (q : GaussianInt[X]) (hd : rawDeterminant rows cols = X^k*q)
    (hy : q.eval₂ GaussianInt.toComplex y ≠ 0) :
    let F := rowFactorial rows
    let B := commonDenominator F q
    0 < B ∧ ∃ R : GaussianInt[X],
      q = C ((Nat.gcd F (gaussianContent q) : ℕ) : GaussianInt)*R ∧
      R.natDegree = q.natDegree ∧ R.eval₂ GaussianInt.toComplex y ≠ 0 ∧
      ∀ x : ℂ, x^k * R.eval₂ GaussianInt.toComplex x = (B : ℂ)*normalizedDetValue rows cols x := by
  let F := rowFactorial rows
  let B := commonDenominator F q
  let g := Nat.gcd F (gaussianContent q)
  have hg : g ≠ 0 := (Nat.gcd_pos_of_pos_left _ (rowFactorial_pos rows)).ne'
  obtain ⟨R,hr⟩ : C (g : GaussianInt) ∣ q := (dvd_gaussianContent_iff _ _).mp (Nat.gcd_dvd_right _ _)
  refine ⟨commonDenominator_pos (rowFactorial_pos rows) q,R,hr,?_,?_,?_⟩
  · rw [hr,natDegree_C_mul (Nat.cast_ne_zero.mpr hg)]
  · intro hz
    rw [hr,eval₂_mul,hz,mul_zero] at hy
    exact hy rfl
  · intro x
    apply mul_left_cancel₀ (show (g : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr hg)
    calc
      (g : ℂ) * (x^k * R.eval₂ GaussianInt.toComplex x) =
          (rawDeterminant rows cols).eval₂ GaussianInt.toComplex x := by
        rw [hd,hr,eval₂_mul,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X,map_natCast]
        ring
      _ = (F : ℂ)*normalizedDetValue rows cols x := by
        rw [rawDeterminant_evaluate]
        simp only [F,rowFactorial,Nat.cast_prod,normalizedDetValue]
      _ = (g : ℂ)*((B : ℂ)*normalizedDetValue rows cols x) := by
        have h : (B : ℂ)*(g : ℂ) = F := by exact_mod_cast commonDenominator_split F q
        rw [← h]
        ring

theorem log_commonDenominator_le {F : ℕ} (hF : 0 < F) (q : GaussianInt[X])
    (E : ℕ → ℕ) (h : ∀ p ∈ F.primeFactors, C ((p^(F.factorization p-E p) : ℕ) : GaussianInt) ∣ q) :
    Real.log (commonDenominator F q : ℝ) ≤ ∑ p ∈ F.primeFactors, (E p : ℝ)*Real.log p := by
  let B := commonDenominator F q
  have hB : 0 < B := commonDenominator_pos hF q
  have hBF : B ∣ F := ⟨_,(commonDenominator_split F q).symm⟩
  have hsub : B.primeFactors ⊆ F.primeFactors := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).mem_primeFactors ((Nat.dvd_of_mem_primeFactors hp).trans hBF) hF.ne'
  have hlog (p : ℕ) (hp : p ∈ F.primeFactors) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
  calc
    Real.log (B : ℝ) = ∑ p ∈ B.primeFactors, (B.factorization p : ℝ)*Real.log (p : ℝ) := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hB.ne']
      simp only [Nat.cast_prod,Nat.cast_pow]
      rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
      simp only [Real.log_pow]
    _ ≤ ∑ p ∈ B.primeFactors, (E p : ℝ)*Real.log (p : ℝ) := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_right _ (hlog p (hsub hp))
      exact_mod_cast commonDenominator_prime_bound (Nat.prime_of_mem_primeFactors hp) hF.ne' q (h p (hsub hp))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => mul_nonneg (Nat.cast_nonneg _) (hlog p hp))

end PiPolynomialValues.FourPeriod
