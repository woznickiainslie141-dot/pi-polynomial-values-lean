module

public import OddPiPowers.PolynomialValues.Endpoint
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Nat.Choose.Bounds

/-! Comparison of the maximum integer coefficient with the multiplicative Mahler measure. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial

noncomputable abbrev measure (P : ℤ[X]) : ℝ := P.mapMahlerMeasure (Int.castRingHom ℂ)

theorem int_natAbs_real (a : ℤ) : (a.natAbs : ℝ) = ‖a‖ := by
  rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

theorem one_le_measure {P : ℤ[X]} (hP : P ≠ 0) : 1 ≤ measure P := by
  have h : 1 ≤ P.leadingCoeff.natAbs :=
    Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hP)
  have hr : (1 : ℝ) ≤ P.leadingCoeff.natAbs := by exact_mod_cast h
  rw [int_natAbs_real] at hr
  exact hr.trans (P.leadingCoeff_le_mapMahlerMeasure _ Complex.isometry_intCast)

theorem height_le_two_pow_mul_measure (P : ℤ[X]) :
    (height P : ℝ) ≤ (2 : ℝ) ^ P.natDegree * measure P := by
  by_cases hP : P = 0
  · simp [hP, height, measure]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup P.support
    (Polynomial.support_nonempty.mpr hP) (fun j => (P.coeff j).natAbs)
  rw [height, hi, int_natAbs_real]
  apply (norm_coeff_le_choose_mul_mapMahlerMeasure (Int.castRingHom ℂ) Complex.isometry_intCast i P).trans
  apply mul_le_mul_of_nonneg_right _ (P.mapMahlerMeasure_nonneg _)
  exact_mod_cast Nat.choose_le_two_pow P.natDegree i

theorem measure_le_degree_mul_height {P : ℤ[X]} {d : ℕ} (hd : P.natDegree ≤ d) :
    measure P ≤ (d + 1 : ℕ) * (height P : ℝ) := by
  apply (P.mapMahlerMeasure_le_sum_norm_coeff _ Complex.isometry_intCast).trans
  rw [P.sum_over_range' (fun _ => norm_zero) (d + 1) (Nat.lt_succ_of_le hd)]
  calc
    _ ≤ ∑ _i ∈ Finset.range (d + 1), (height P : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← int_natAbs_real]
      exact_mod_cast coeff_natAbs_le_height P i
    _ = _ := by simp

theorem measure_mul (P Q : ℤ[X]) : measure (P * Q) = measure P * measure Q :=
  mapMahlerMeasure_mul _ P Q

theorem measure_C (a : ℤ) : measure (C a) = |(a : ℝ)| :=
  (mapMahlerMeasure_const _ Complex.isometry_intCast a).trans (Int.norm_eq_abs a)

end PiPolynomialValues
