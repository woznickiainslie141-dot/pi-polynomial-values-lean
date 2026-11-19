module

public import OddPiPowers.Foundations.GaussianFraction
public import OddPiPowers.Transfer.MinimalResultant
public import Mathlib.Analysis.Complex.Basic

/-! A fixed Gaussian integer annihilator supplies one primitive factor that can
be used with every auxiliary polynomial at the same algebraic point. -/

@[expose] public section

namespace PiPolynomialValues

open OddPiPowers Polynomial

noncomputable local instance : Algebra GaussianFraction ℂ := gaussianFractionEmbedding.toAlgebra
noncomputable local instance : NormalizedGCDMonoid GaussianInt := Classical.choice inferInstance

theorem exists_gaussian_fixed_factor (F : GaussianInt[X]) (x : ℂ) (hF : F ≠ 0)
    (hx : F.eval₂ GaussianInt.toComplex x = 0) :
    ∃ f : GaussianInt[X], f ≠ 0 ∧ f.natDegree ≤ F.natDegree ∧ f.eval₂ GaussianInt.toComplex x = 0 ∧
      ∀ R : GaussianInt[X], R.eval₂ GaussianInt.toComplex x ≠ 0 → resultant f R ≠ 0 := by
  have hcomp : (algebraMap GaussianFraction ℂ).comp
      (algebraMap GaussianInt GaussianFraction) = GaussianInt.toComplex := gaussianFractionEmbedding_comp
  have halg : IsIntegral GaussianFraction x := by
    apply IsAlgebraic.isIntegral
    refine ⟨F.map (algebraMap GaussianInt GaussianFraction),
      (Polynomial.map_ne_zero_iff (IsFractionRing.injective _ _)).mpr hF, ?_⟩
    rw [aeval_def, eval₂_map, hcomp, hx]
  let f := primitiveNormalization (R := GaussianInt) (minpoly GaussianFraction x)
  have hdiv : f ∣ F :=
    primitive_minpoly_dvd x F (by simpa only [hcomp] using hx)
  refine ⟨f, (primitiveNormalization_isPrimitive (R := GaussianInt) _).ne_zero,
    natDegree_le_of_dvd hdiv hF, ?_, ?_⟩
  · simpa only [hcomp] using primitive_minpoly_eval₂_eq_zero (R := GaussianInt) x halg
  · intro R hR
    exact primitive_minpoly_resultant_ne_zero x halg R (by simpa only [hcomp] using hR)

end PiPolynomialValues
