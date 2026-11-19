module

public import OddPiPowers.PolynomialValues.MahlerHeight
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Root-difference products for the actual integer discriminants of quadratics
and cubics. The original leading coefficient is retained at its sharp power. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial

theorem roots_nodup_of_rational_irreducible {p : ℤ[X]}
    (hp : Irreducible (p.map (Int.castRingHom ℚ))) :
    (p.map (Int.castRingHom ℂ)).roots.Nodup := by
  have h := (PerfectField.separable_of_irreducible hp).map (f := Rat.castHom ℂ)
  have hcomp : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := Subsingleton.elim _ _
  rw [map_map, hcomp] at h
  exact nodup_roots h

theorem quadratic_discriminant_roots (p : ℤ[X]) (hd : p.degree = 2)
    (x y : ℂ) (hr : (p.map (Int.castRingHom ℂ)).roots = {x, y}) :
    (p.discr : ℂ) = ((p.leadingCoeff : ℂ) * (x - y)) ^ 2 := by
  let a : ℂ := p.leadingCoeff
  let P := p.map (Int.castRingHom ℂ)
  have hι : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hf : P = C a * (X - C x) * (X - C y) := by
    calc
      P = C P.leadingCoeff * (P.roots.map (X - C ·)).prod := (IsAlgClosed.splits P).eq_prod_roots
      _ = _ := by
        change C (p.map (Int.castRingHom ℂ)).leadingCoeff * ((p.map (Int.castRingHom ℂ)).roots.map _).prod = _
        rw [hr, leadingCoeff_map_of_injective hι]
        simp [a, mul_assoc]
  have he : P = C a * X ^ 2 + C (-(a * (x + y))) * X + C (a * x * y) := by
    rw [hf]
    simp only [map_add, map_mul, map_neg]
    ring
  have h0 : (p.coeff 0 : ℂ) = a * x * y := by
    simpa [P, coeff_add, coeff_C, coeff_C_mul_X_pow, coeff_C_mul_X] using
      congrArg (fun q : ℂ[X] => q.coeff 0) he
  have h1 : (p.coeff 1 : ℂ) = -(a * (x + y)) := by
    simpa [P, coeff_add, coeff_C, coeff_C_mul_X_pow, coeff_C_mul_X] using
      congrArg (fun q : ℂ[X] => q.coeff 1) he
  have hn : p.natDegree = 2 := natDegree_eq_of_degree_eq_some hd
  have ha : (p.coeff 2 : ℂ) = a := by rw [← hn, coeff_natDegree]
  rw [discr_of_degree_eq_two hd]
  push_cast
  rw [h0, h1, ha]
  change _ = (a * (x - y)) ^ 2
  ring

theorem cubic_discriminant_roots (p : ℤ[X]) (hd : p.degree = 3)
    (x y z : ℂ) (hr : (p.map (Int.castRingHom ℂ)).roots = {x, y, z}) :
    (p.discr : ℂ) = ((p.leadingCoeff : ℂ) ^ 2 * (x - y) * (x - z) * (y - z)) ^ 2 := by
  let a : ℂ := p.leadingCoeff
  let P := p.map (Int.castRingHom ℂ)
  have hι : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hf : P = C a * (X - C x) * (X - C y) * (X - C z) := by
    calc
      P = C P.leadingCoeff * (P.roots.map (X - C ·)).prod := (IsAlgClosed.splits P).eq_prod_roots
      _ = _ := by
        change C (p.map (Int.castRingHom ℂ)).leadingCoeff * ((p.map (Int.castRingHom ℂ)).roots.map _).prod = _
        rw [hr, leadingCoeff_map_of_injective hι]
        simp [a, mul_assoc]
  have he : P = C a * X ^ 3 + C (-(a * (x + y + z))) * X ^ 2 + C (a * (x * y + x * z + y * z)) * X + C (-(a * (x * y * z))) := by
    rw [hf]
    simp only [map_add, map_mul, map_neg]
    ring
  have h0 : (p.coeff 0 : ℂ) = -(a * (x * y * z)) := by
    simpa [P, coeff_add, coeff_C, coeff_C_mul_X_pow, coeff_C_mul_X] using
      congrArg (fun q : ℂ[X] => q.coeff 0) he
  have h1 : (p.coeff 1 : ℂ) = a * (x * y + x * z + y * z) := by
    have ht := congrArg (fun q : ℂ[X] => q.coeff 1) he
    simp only [P, coeff_map, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at ht
    simpa using ht
  have h2 : (p.coeff 2 : ℂ) = -(a * (x + y + z)) := by
    have ht := congrArg (fun q : ℂ[X] => q.coeff 2) he
    simp only [P, coeff_map, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at ht
    simpa using ht
  have hn : p.natDegree = 3 := natDegree_eq_of_degree_eq_some hd
  have ha : (p.coeff 3 : ℂ) = a := by rw [← hn, coeff_natDegree]
  rw [discr_of_degree_eq_three hd]
  push_cast
  rw [h0, h1, h2, ha]
  change _ = (a ^ 2 * (x - y) * (x - z) * (y - z)) ^ 2
  ring

theorem one_le_norm_of_discriminant_square (p : ℤ[X]) {v : ℂ} (hv : v ≠ 0)
    (hdisc : (p.discr : ℂ) = v ^ 2) : 1 ≤ ‖v‖ := by
  have hne : p.discr ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hdisc
    exact (pow_ne_zero 2 hv) hdisc.symm
  have ha : (1 : ℝ) ≤ (p.discr.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hne
  rw [int_natAbs_real] at ha
  have hn := congrArg norm hdisc
  rw [Complex.norm_intCast, norm_pow] at hn
  exact (one_le_pow_iff_of_nonneg (norm_nonneg v) (by decide : 2 ≠ 0)).mp (hn ▸ ha)

end PiPolynomialValues
