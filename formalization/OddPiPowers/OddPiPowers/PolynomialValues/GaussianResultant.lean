module

public import OddPiPowers.PolynomialValues.IntegerResultant

/-! The Gaussian resultant keeps the separate evaluations of a single polynomial
at all conjugate roots, with their multiplicities. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial

theorem gaussian_resultant_ne_zero_at_real_root (f : ℤ[X]) (R : GaussianInt[X]) (x : ℝ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hf : f.eval₂ (Int.castRingHom ℂ) (x : ℂ) = 0)
    (hR : R.eval₂ GaussianInt.toComplex (x : ℂ) ≠ 0) :
    resultant (f.map (Int.castRingHom GaussianInt)) R ≠ 0 := by
  let ι := Int.castRingHom GaussianInt
  let σ := starRingEnd GaussianInt
  have hι : Function.Injective ι := Int.cast_injective
  have hσ : Function.Injective σ := (starRingAut : GaussianInt ≃+* GaussianInt).injective
  obtain ⟨S, hS, hres⟩ := exists_int_resultant_for_gaussian f R x hirr hf hR
  have hn : R ≠ 0 := fun h => hR (by simp [h])
  have hsn : R.map σ ≠ 0 := (Polynomial.map_ne_zero_iff hσ).mpr hn
  have hh : resultant (f.map ι) (S.map ι) ≠ 0 := by
    rw [natDegree_map_eq_of_injective hι, natDegree_map_eq_of_injective hι, resultant_map_map]
    exact (map_ne_zero_iff _ hι).mpr hres
  change S.map ι = R * R.map σ at hS
  rw [hS, natDegree_mul hn hsn, resultant_mul_right _ _ _ _ le_rfl] at hh
  exact left_ne_zero_of_mul hh

/-- Exact product lower bound over the roots of the original integer polynomial. -/
theorem one_le_gaussian_root_product (f : ℤ[X]) (R : GaussianInt[X]) (x : ℝ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hf : f.eval₂ (Int.castRingHom ℂ) (x : ℂ) = 0)
    (hR : R.eval₂ GaussianInt.toComplex (x : ℂ) ≠ 0) :
    1 ≤ ‖(f.leadingCoeff : ℂ)‖ ^ R.natDegree *
      ((f.map (Int.castRingHom ℂ)).roots.map (fun z => ‖R.eval₂ GaussianInt.toComplex z‖)).prod := by
  let ι := Int.castRingHom GaussianInt
  let φ := GaussianInt.toComplex
  have hι : Function.Injective ι := Int.cast_injective
  have hφ := GaussianInt.toComplex_injective
  have hcomp : φ.comp ι = Int.castRingHom ℂ := Subsingleton.elim _ _
  let F := f.map ι
  have hres := gaussian_resultant_ne_zero_at_real_root f R x hirr hf hR
  have hbound := OddPiPowers.gaussian_norm_ge_one (resultant F R) hres
  have heq := resultant_eq_prod_eval (F.map φ) (R.map φ) (R.map φ).natDegree
    le_rfl (IsAlgClosed.splits _)
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ, resultant_map_map] at heq
  change 1 ≤ ‖φ (resultant F R)‖ at hbound
  rw [heq, norm_mul, norm_pow, Multiset.norm_prod_map] at hbound
  have hℂ : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  simp only [F, map_map, hcomp, leadingCoeff_map_of_injective hℂ, Int.coe_castRingHom,
    eval_map] at hbound
  exact hbound

end PiPolynomialValues
