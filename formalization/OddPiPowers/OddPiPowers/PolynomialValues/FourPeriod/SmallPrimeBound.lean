module

public import OddPiPowers.PolynomialValues.FourPeriod.NewtonDeterminant
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The small-prime part of the actual common denominator has a
uniform square-root times logarithm loss per derivative layer sum. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset Real Filter

theorem quotient_prime_cost {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ) (q : GaussianInt[X]) (k S p : ℕ)
    (hp : p.Prime) (hS : ∀ i, (e i).2.val ≤ S)
    (hdet : rawDeterminant (fun i => (node (e i).1,(e i).2.val)) cols = X^k*q) :
    let rows := fun i => (node (e i).1,(e i).2.val)
    (commonDenominator (rowFactorial rows) q).factorization p ≤ p.log S * (∑ j, (cols j).2) := by
  let rows := fun i => (node (e i).1,(e i).2.val)
  apply commonDenominator_prime_bound hp (rowFactorial_pos rows).ne'
  apply (C_dvd_strip_origin _ k q).mp
  rw [← hdet]
  exact rawDeterminant_prime_dvd e node cols p (p.log S) hp (fun i => Nat.log_mono_right (hS i))

theorem small_prime_log_sum {S J : ℕ} (hS : 0 < S) (P : Finset ℕ) (E : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ p*p ≤ S ∧ E p ≤ p.log S*J) :
    (∑ p ∈ P, (E p : ℝ)*Real.log (p : ℝ)) ≤ ((Nat.sqrt S : ℕ) : ℝ)*J*Real.log S := by
  have hcard : P.card ≤ Nat.sqrt S := by
    have hs : P ⊆ Icc 1 (Nat.sqrt S) := fun p h => mem_Icc.mpr
      ⟨(hp p h).1.one_le,Nat.le_sqrt.mpr (hp p h).2.1⟩
    simpa using card_le_card hs
  calc
    _ ≤ ∑ _p ∈ P, (J : ℝ)*Real.log (S : ℝ) := by
      apply sum_le_sum
      intro p h
      obtain ⟨hprime,_,hc⟩ := hp p h
      have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
      have hpow : (p : ℝ)^(p.log S) ≤ S := by exact_mod_cast Nat.pow_log_le_self p hS.ne'
      have hlog := Real.log_le_log (pow_pos (show (0 : ℝ) < p by exact_mod_cast hprime.pos) _) hpow
      rw [Real.log_pow] at hlog
      calc
        _ ≤ ((p.log S : ℝ)*J)*Real.log (p : ℝ) := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hl
        _ = (J : ℝ)*((p.log S : ℝ)*Real.log (p : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [sum_const,nsmul_eq_mul,← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _))
        (Real.log_nonneg (by exact_mod_cast hS))

theorem sqrt_log_over_scale_tendsto :
    Tendsto (fun s : ℝ => Real.sqrt s * Real.log s / s) atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [← Real.sqrt_eq_rpow]
  have hh := Real.sq_sqrt hs.le
  have hpos := Real.sqrt_pos.mpr hs
  field_simp
  nlinarith [congrArg (fun u : ℝ => u*Real.log s) hh]

end PiPolynomialValues.FourPeriod
