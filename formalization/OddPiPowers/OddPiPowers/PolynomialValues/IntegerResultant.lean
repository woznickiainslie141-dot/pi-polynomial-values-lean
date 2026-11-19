module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import OddPiPowers.Foundations.GaussianArithmetic

/-! Descent of a Gaussian polynomial times its coefficient conjugate to the integers. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial
open scoped ComplexConjugate

/-- A single nonzero evaluation at a root of a rationally irreducible polynomial
gives a nonzero integer resultant. Primitivity of the integer representative is unnecessary. -/
theorem int_resultant_ne_zero_at_root {K : Type*} [Field K] [CharZero K]
    (f S : ℤ[X]) (x : K) (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hf : f.eval₂ (Int.castRingHom K) x = 0) (hS : S.eval₂ (Int.castRingHom K) x ≠ 0) :
    resultant f S ≠ 0 := by
  let ι := Int.castRingHom ℚ
  have hcomp : (Rat.castHom K).comp ι = Int.castRingHom K := Subsingleton.elim _ _
  have hnd : ¬ f.map ι ∣ S.map ι := by
    rintro ⟨q, hq⟩
    apply hS
    rw [← hcomp, ← eval₂_map, hq, eval₂_mul, eval₂_map, hcomp, hf, zero_mul]
  have hres := resultant_ne_zero (f.map ι) (S.map ι) (hirr.coprime_iff_not_dvd.mpr hnd)
  have hinj : Function.Injective ι := Int.cast_injective
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at hres
  intro hzero
  exact hres (hzero ▸ map_zero ι)

/-- Coefficient conjugation commutes with evaluation at a real argument. -/
theorem eval_conjugate_at_real (R : GaussianInt[X]) (x : ℝ) :
    (R.map (starRingEnd GaussianInt)).eval₂ GaussianInt.toComplex (x : ℂ) =
      conj (R.eval₂ GaussianInt.toComplex (x : ℂ)) := by
  have hcomp : GaussianInt.toComplex.comp (starRingEnd GaussianInt) =
      (starRingEnd ℂ).comp GaussianInt.toComplex :=
    RingHom.ext fun z => GaussianInt.toComplex_star z
  rw [eval₂_map, hcomp]
  have hx : starRingEnd ℂ (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simpa only [hx] using
    (hom_eval₂ R GaussianInt.toComplex (starRingEnd ℂ) (x : ℂ)).symm

/-- Every coefficient of the product with the conjugate has zero imaginary part. -/
theorem exists_int_conjugate_product (R : GaussianInt[X]) :
    ∃ S : ℤ[X], S.map (Int.castRingHom GaussianInt) = R * R.map (starRingEnd GaussianInt) := by
  let σ := starRingEnd GaussianInt
  let T := R * R.map σ
  have hσσ : σ.comp σ = RingHom.id GaussianInt := RingHom.ext fun z => star_star z
  have hfixed : T.map σ = T := by
    simp only [T, Polynomial.map_mul, map_map, hσσ, map_id]
    exact mul_comm _ _
  apply (lifts_iff_set_range T).mp
  apply (lifts_iff_coeff_lifts T).mpr
  intro n
  have hs : star (T.coeff n) = T.coeff n := by
    change σ (T.coeff n) = T.coeff n
    simpa only [coeff_map] using congrArg (fun p : GaussianInt[X] => p.coeff n) hfixed
  have hi := congrArg (fun z : GaussianInt => z.im) hs
  change -(T.coeff n).im = (T.coeff n).im at hi
  refine ⟨(T.coeff n).re, Zsqrtd.ext ?_ ?_⟩
  · exact Zsqrtd.re_intCast _
  · change (((T.coeff n).re : GaussianInt)).im = (T.coeff n).im
    rw [Zsqrtd.im_intCast]
    omega

/-- The restricted norm gives an integer polynomial whose value at the selected real
root and whose integer resultant are both nonzero. -/
theorem exists_int_resultant_for_gaussian (f : ℤ[X]) (R : GaussianInt[X]) (x : ℝ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hf : f.eval₂ (Int.castRingHom ℂ) (x : ℂ) = 0)
    (hR : R.eval₂ GaussianInt.toComplex (x : ℂ) ≠ 0) :
    ∃ S : ℤ[X], S.map (Int.castRingHom GaussianInt) = R * R.map (starRingEnd GaussianInt) ∧
      resultant f S ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_int_conjugate_product R
  refine ⟨S, hS, int_resultant_ne_zero_at_root f S (x : ℂ) hirr hf ?_⟩
  have hcomp : GaussianInt.toComplex.comp (Int.castRingHom GaussianInt) = Int.castRingHom ℂ :=
    Subsingleton.elim _ _
  rw [← hcomp, ← eval₂_map, hS, eval₂_mul, eval_conjugate_at_real]
  exact mul_ne_zero hR ((map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr hR)

end PiPolynomialValues

