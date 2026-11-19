module

public import OddPiPowers.PolynomialValues.FourPeriod.Symbol
public import Mathlib.Algebra.Polynomial.BigOperators

/-! Each column is cleared using its own bandwidth. This gives an actual
ordinary polynomial with degree at most twice the sum of the bandwidths. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

noncomputable def frequencyEntry (S : Finset ℤ) (p : ℤ → ℂ[X]) (U r k : ℕ) : ℂ[X] :=
  ∑ t ∈ S, X ^ shiftedFrequency U t *
    C ((rowOperator 1 (t : ℂ) r (Polynomial.derivative^[k] (p t))).coeff 0)

theorem symbolEntry_at_zero (S : Finset ℤ) (p : ℤ → ℂ[X]) (U r k : ℕ) :
    (evalRingHom (0 : ℂ[X])) (symbolEntry S p U r k) = frequencyEntry S p U r k := by
  unfold symbolEntry frequencyEntry
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_mul, coe_evalRingHom, eval_C, eval_zero_map, ← coeff_zero_eq_eval_zero]

theorem symbolPolynomial_eq_frequency_det (S : Finset ℤ) (p : ℤ → ℂ[X]) (U J : ℕ) :
    symbolPolynomial S p U J = (Matrix.of (fun (r k : Fin (J + 1)) =>
      frequencyEntry S p U r.val k.val)).det := by
  unfold symbolPolynomial
  rw [coeff_zero_eq_eval_zero, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro r k
  exact symbolEntry_at_zero S p U r.val k.val

/-- Bounds on exactly those frequency terms which survive k derivatives. -/
def InBand (S : Finset ℤ) (p : ℤ → ℂ[X]) (k B : ℕ) : Prop :=
  ∀ t ∈ S, Polynomial.derivative^[k] (p t) ≠ 0 → -(B : ℤ) ≤ t ∧ t ≤ B

theorem frequencyEntry_degree (S : Finset ℤ) (p : ℤ → ℂ[X]) (B r k : ℕ)
    (hb : InBand S p k B) :
    (frequencyEntry S p B r k).natDegree ≤ 2 * B := by
  apply natDegree_sum_le_of_forall_le
  intro t ht
  by_cases hz : Polynomial.derivative^[k] (p t) = 0
  · simp [hz, rowOperator_zero]
  · apply (natDegree_mul_le ..).trans
    rw [natDegree_C, Nat.add_zero, natDegree_X_pow]
    have := hb t ht hz
    unfold shiftedFrequency
    omega

theorem frequencyEntry_shift (S : Finset ℤ) (p : ℤ → ℂ[X]) (U B r k : ℕ)
    (hle : B ≤ U) (hb : InBand S p k B) :
    frequencyEntry S p U r k = X ^ (U - B) * frequencyEntry S p B r k := by
  simp only [frequencyEntry, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hz : Polynomial.derivative^[k] (p t) = 0
  · simp [hz, rowOperator_zero]
  · have hlo := (hb t ht hz).1
    have h : shiftedFrequency U t = U - B + shiftedFrequency B t := by
      unfold shiftedFrequency
      omega
    rw [h, pow_add, mul_assoc]

noncomputable def bandMatrix {J : ℕ} (S : Finset ℤ) (p : ℤ → ℂ[X])
    (B : Fin (J + 1) → ℕ) : Matrix (Fin (J + 1)) (Fin (J + 1)) ℂ[X] :=
  Matrix.of fun r k => frequencyEntry S p (B k) r.val k.val

theorem bandDeterminant_degree {J : ℕ} (S : Finset ℤ) (p : ℤ → ℂ[X]) (B : Fin (J + 1) → ℕ)
    (hb : ∀ k, InBand S p k.val (B k)) :
    (bandMatrix S p B).det.natDegree ≤ ∑ k, 2 * B k := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le Finset.univ _).trans
  exact Finset.sum_le_sum fun k _ => frequencyEntry_degree S p (B k) (σ k).val k.val (hb k)

theorem symbolPolynomial_factor {J : ℕ} (S : Finset ℤ) (p : ℤ → ℂ[X]) (U : ℕ)
    (B : Fin (J + 1) → ℕ) (hle : ∀ k, B k ≤ U) (hb : ∀ k, InBand S p k.val (B k)) :
    symbolPolynomial S p U J = (bandMatrix S p B).det * (∏ k, X ^ (U - B k)) := by
  rw [symbolPolynomial_eq_frequency_det, ← Matrix.det_diagonal, ← Matrix.det_mul]
  congr 1
  apply Matrix.ext
  intro r k
  rw [Matrix.mul_diagonal]
  exact (frequencyEntry_shift S p U (B k) r.val k.val (hle k) (hb k)).trans (mul_comm ..)

end PiPolynomialValues.FourPeriod
