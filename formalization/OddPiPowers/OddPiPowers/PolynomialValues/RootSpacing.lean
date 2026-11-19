module

public import OddPiPowers.PolynomialValues.RootDiscriminant
public import OddPiPowers.PolynomialValues.NormalizedResultant

/-! The integer discriminant controls all secondary relative root distances
at once. A uniquely closest conjugate of a real number is real. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial Complex
open scoped ComplexConjugate

theorem quadratic_secondary_distance (p : ℤ[X]) (hp : p.degree=2) (ξ x y : ℂ)
    (hxy : x≠y) (hr : (p.map (Int.castRingHom ℂ)).roots={x,y})
    (ho : truncatedDistance ξ x≤truncatedDistance ξ y) :
    1≤measure p*(2*(1+‖ξ‖))*truncatedDistance ξ y := by
  have hn : p≠0 := fun h => by simp [h] at hp
  have ha : (p.leadingCoeff : ℂ)≠0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hn
  have h := one_le_norm_of_discriminant_square p (mul_ne_zero ha (sub_ne_zero.mpr hxy))
    (quadratic_discriminant_roots p hp x y hr)
  rw [norm_mul] at h
  have H := mul_le_mul_of_nonneg_left (root_pair_distance_le ξ x y ho) (norm_nonneg (p.leadingCoeff : ℂ))
  rw [measure_rootScale,hr]
  simpa only [Multiset.insert_eq_cons,Multiset.map_cons,Multiset.map_singleton,Multiset.prod_cons,Multiset.prod_singleton,mul_assoc] using h.trans H

theorem cubic_secondary_distances (p : ℤ[X]) (hp : p.degree=3) (ξ x y z : ℂ)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (hr : (p.map (Int.castRingHom ℂ)).roots={x,y,z})
    (h₁ : truncatedDistance ξ x≤truncatedDistance ξ y)
    (h₂ : truncatedDistance ξ y≤truncatedDistance ξ z) :
    1≤(measure p)^2*(2*(1+‖ξ‖))^3*truncatedDistance ξ y*(truncatedDistance ξ z)^2 := by
  have hn : p≠0 := fun h => by simp [h] at hp
  have ha : (p.leadingCoeff : ℂ)≠0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hn
  have h := one_le_norm_of_discriminant_square p
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (sub_ne_zero.mpr hxy)) (sub_ne_zero.mpr hxz)) (sub_ne_zero.mpr hyz))
    (cubic_discriminant_roots p hp x y z hr)
  simp only [norm_mul,norm_pow] at h
  have H := mul_le_mul_of_nonneg_left (root_pair_distance_le ξ x y h₁) (sq_nonneg ‖(p.leadingCoeff : ℂ)‖)
  have J := mul_le_mul H (root_pair_distance_le ξ x z (h₁.trans h₂)) (norm_nonneg _) ((mul_nonneg (sq_nonneg _) (norm_nonneg _)).trans H)
  have K := mul_le_mul J (root_pair_distance_le ξ y z h₂) (norm_nonneg _)
    ((mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (norm_nonneg _)).trans J)
  apply (h.trans K).trans_eq
  rw [measure_rootScale,hr]
  simp only [Multiset.insert_eq_cons,Multiset.map_cons,Multiset.map_singleton,Multiset.prod_cons,Multiset.prod_singleton]
  ring

theorem rootScale_conj (z : ℂ) : rootScale (conj z)=rootScale z := by simp [rootScale]

theorem truncatedDistance_conj (ξ : ℝ) (z : ℂ) :
    truncatedDistance (ξ : ℂ) (conj z)=truncatedDistance (ξ : ℂ) z := by
  simp only [truncatedDistance,relativeDistance,rootScale_conj]
  rw [show (ξ : ℂ)-conj z=conj ((ξ : ℂ)-z) by simp,Complex.norm_conj]

theorem integer_root_conj {p : ℤ[X]} {z : ℂ} (hz : z ∈ (p.map (Int.castRingHom ℂ)).roots) :
    conj z ∈ (p.map (Int.castRingHom ℂ)).roots := by
  let f := p.map (Int.castRingHom ℂ)
  have hn : f≠0 := by intro he; simp [← show f=p.map (Int.castRingHom ℂ) from rfl,he] at hz
  have he := (mem_roots hn).mp hz
  have hmap : f.map (starRingEnd ℂ)=f := by rw [show f=p.map (Int.castRingHom ℂ) from rfl,map_map]; congr 1; exact Subsingleton.elim _ _
  apply (mem_roots hn).mpr
  change f.eval (conj z)=0
  calc
    _ = (f.map (starRingEnd ℂ)).eval (conj z) := by rw [hmap]
    _ = conj (f.eval z) := by rw [eval_map_apply]
    _ = 0 := by rw [show f.eval z=0 from he,map_zero]

theorem closest_root_real {p : ℤ[X]} (ξ : ℝ) {z : ℂ} (hz : z ∈ (p.map (Int.castRingHom ℂ)).roots)
    (hu : ∀ w ∈ (p.map (Int.castRingHom ℂ)).roots, truncatedDistance (ξ : ℂ) w ≤ truncatedDistance (ξ : ℂ) z → w=z) :
    ∃ x : ℝ, z=(x : ℂ) :=
  Complex.conj_eq_iff_real.mp (hu _ (integer_root_conj hz) (truncatedDistance_conj ξ z).le)

end PiPolynomialValues
