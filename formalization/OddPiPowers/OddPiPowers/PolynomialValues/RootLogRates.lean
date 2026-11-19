module

public import OddPiPowers.PolynomialValues.RootSpacing
public import OddPiPowers.PolynomialValues.EscapingInputs

/-! A small polynomial value forces a large total logarithmic proximity
among the actual conjugates on the Mahler scale. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial Real

noncomputable def rootProximity (ξ z : ℂ) := -log (truncatedDistance ξ z)

theorem rootProximity_nonneg (ξ z : ℂ) : 0≤rootProximity ξ z :=
  neg_nonneg.mpr (Real.log_nonpos (truncatedDistance_nonneg ξ z) (min_le_left _ _))

theorem root_proximity_budget (p : ℤ[X]) (ξ : ℝ) (hp : p≠0) (hval : value ξ p≠0) :
    log (measure p)-log |value ξ p|≤((p.map (Int.castRingHom ℂ)).roots.map (rootProximity (ξ : ℂ))).sum := by
  let s := (p.map (Int.castRingHom ℂ)).roots
  let v := relativeDistance (ξ : ℂ)
  have he := norm_eval_eq_measure_mul_relative p (ξ : ℂ)
  rw [complex_value_at_real,Complex.norm_real,Real.norm_eq_abs] at he
  change |value ξ p|=measure p*(s.map v).prod at he
  have hM : 0<measure p := zero_lt_one.trans_le (one_le_measure hp)
  have hprod : (s.map v).prod≠0 := right_ne_zero_of_mul (he ▸ (abs_pos.mpr hval).ne')
  have hr (z : ℂ) (hz : z∈s) : 0<v z := lt_of_le_of_ne (relativeDistance_nonneg _ _) (by
    intro H
    apply hprod
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨z,hz,H.symm⟩))
  rw [he,Real.log_mul hM.ne' hprod,Real.log_multiset_prod (fun y hy he => hprod (by subst y; exact Multiset.prod_eq_zero hy)),
    Multiset.map_map]
  have bound (u : Multiset ℂ) (hu : ∀ z∈u, 0<v z) :
      -(u.map (fun z => log (v z))).sum≤(u.map (rootProximity (ξ : ℂ))).sum := by
    induction u using Multiset.induction_on with
    | empty => simp
    | cons z u ih =>
      have hhead := Real.log_le_log (lt_min zero_lt_one (hu z (by simp))) (min_le_right 1 (v z))
      have htail := ih (fun y hy => hu y (Multiset.mem_cons_of_mem hy))
      simp only [Multiset.map_cons,Multiset.sum_cons,neg_add_rev]
      change _≤ -log (min 1 (v z))+_
      linarith only [hhead,htail]
  change log (measure p)-(log (measure p)+(s.map (fun z => log (v z))).sum)≤_
  linarith only [bound s hr]

theorem small_value_budget {d : ℕ} {w ξ : ℝ} (p : ℤ[X]) (hp : p≠0) (hd : p.natDegree≤d)
    (hw : 0≤w) (hv : value ξ p≠0) (hsmall : |value ξ p|<(height p : ℝ)^(-w)) :
    (1+w)*log (measure p)-w*log ((d : ℝ)+1)≤
      ((p.map (Int.castRingHom ℂ)).roots.map (rootProximity (ξ : ℂ))).sum := by
  have hH : 0<(height p : ℝ) := by exact_mod_cast height_pos hp
  have hM : 0<measure p := zero_lt_one.trans_le (one_le_measure hp)
  have h := Real.log_lt_log (abs_pos.mpr hv) hsmall
  rw [Real.log_rpow hH] at h
  have hmh := Real.log_le_log hM (measure_le_degree_mul_height hd)
  rw [Real.log_mul (by positivity) hH.ne'] at hmh
  push_cast at hmh
  apply (le_trans _ (root_proximity_budget p ξ hp hv))
  nlinarith only [h,mul_le_mul_of_nonneg_left hmh hw]

end PiPolynomialValues
