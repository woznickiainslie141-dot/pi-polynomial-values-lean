module

public import OddPiPowers.PolynomialValues.GaussianResultant
public import OddPiPowers.PolynomialValues.RootDistances

/-! The resultant obstruction after normalizing each conjugate by its
own root scale. Its logarithm retains the degree of the same witness. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial Real

theorem measure_rootScale (p : ℤ[X]) : measure p = ‖(p.leadingCoeff : ℂ)‖*
    ((p.map (Int.castRingHom ℂ)).roots.map rootScale).prod := by
  change (p.map (Int.castRingHom ℂ)).mahlerMeasure=_
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots,leadingCoeff_map_of_injective (Int.cast_injective (α := ℂ))]
  rfl

theorem rootScale_product_cancel (s : Multiset ℂ) (v : ℂ → ℝ) (d : ℕ) :
    ((s.map rootScale).prod)^d*(s.map (fun z => v z/(rootScale z)^d)).prod=(s.map v).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons,mul_pow]
    rw [mul_mul_mul_comm,mul_div_cancel₀ _ (pow_ne_zero _ (rootScale_pos z).ne'),ih]

noncomputable def reducedEvaluation (R : GaussianInt[X]) (z : ℂ) :=
  ‖R.eval₂ GaussianInt.toComplex z‖/(rootScale z)^R.natDegree

theorem one_le_reduced_resultant (f : ℤ[X]) (R : GaussianInt[X]) (x : ℝ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hf : f.eval₂ (Int.castRingHom ℂ) (x : ℂ)=0) (hR : R.eval₂ GaussianInt.toComplex (x : ℂ)≠0) :
    1 ≤ (measure f)^R.natDegree*((f.map (Int.castRingHom ℂ)).roots.map (reducedEvaluation R)).prod := by
  rw [measure_rootScale,mul_pow,mul_assoc]
  change 1≤_*( _*((f.map (Int.castRingHom ℂ)).roots.map
    (fun z => ‖R.eval₂ GaussianInt.toComplex z‖/(rootScale z)^R.natDegree)).prod)
  rw [rootScale_product_cancel]
  exact one_le_gaussian_root_product f R x hirr hf hR

theorem log_resultant_obstruction (f : ℤ[X]) (R : GaussianInt[X]) (x : ℝ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hf : f.eval₂ (Int.castRingHom ℂ) (x : ℂ)=0) (hR : R.eval₂ GaussianInt.toComplex (x : ℂ)≠0) :
    0 ≤ R.natDegree*Real.log (measure f)+
      ((f.map (Int.castRingHom ℂ)).roots.map (fun z => Real.log (reducedEvaluation R z))).sum := by
  have H := one_le_reduced_resultant f R x hirr hf hR
  let s := (f.map (Int.castRingHom ℂ)).roots.map (reducedEvaluation R)
  have hp : 0<(measure f)^R.natDegree*s.prod := zero_lt_one.trans_le H
  have h₁ := left_ne_zero_of_mul hp.ne'
  have h₂ := right_ne_zero_of_mul hp.ne'
  have hlog := Real.log_nonneg H
  change 0≤Real.log ((measure f)^R.natDegree*s.prod) at hlog
  rw [Real.log_mul h₁ h₂,Real.log_pow,Real.log_multiset_prod (fun y hy he => h₂ (by subst y; exact Multiset.prod_eq_zero hy))] at hlog
  simpa only [s,Multiset.map_map,Function.comp_def] using hlog

end PiPolynomialValues
