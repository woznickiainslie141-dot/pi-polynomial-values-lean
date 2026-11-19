module

public import OddPiPowers.PolynomialValues.RootLogRates
public import Mathlib.Data.List.Sort
public import Mathlib.FieldTheory.Separable

/-! Order the actual complex conjugates and translate the quadratic and cubic
discriminant bounds to the sum of their secondary logarithmic proximities. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial Real

noncomputable def orderedRoots (p : ℤ[X]) (ξ : ℂ) : List ℂ :=
  (p.map (Int.castRingHom ℂ)).roots.toList.mergeSort
    (fun x y => decide (truncatedDistance ξ x≤truncatedDistance ξ y))

theorem orderedRoots_multiset (p : ℤ[X]) (ξ : ℂ) :
    (↑(orderedRoots p ξ) : Multiset ℂ)=(p.map (Int.castRingHom ℂ)).roots := by
  unfold orderedRoots
  rw [Multiset.coe_eq_coe.mpr (List.mergeSort_perm _ _),Multiset.coe_toList]

theorem orderedRoots_length (p : ℤ[X]) (ξ : ℂ) : (orderedRoots p ξ).length=p.natDegree := by
  rw [← Multiset.coe_card,orderedRoots_multiset,← (IsAlgClosed.splits _).natDegree_eq_card_roots,
    natDegree_map_eq_of_injective (Int.cast_injective (α := ℂ))]

theorem orderedRoots_pairwise (p : ℤ[X]) (ξ : ℂ) :
    (orderedRoots p ξ).Pairwise (fun x y => truncatedDistance ξ x≤truncatedDistance ξ y) := by
  simpa only [orderedRoots,decide_eq_true_eq] using (p.map (Int.castRingHom ℂ)).roots.toList.pairwise_mergeSort
    (le := fun x y => decide (truncatedDistance ξ x≤truncatedDistance ξ y))
    (fun a b c => by simpa only [decide_eq_true_eq] using
      (le_trans : truncatedDistance ξ a≤truncatedDistance ξ b → truncatedDistance ξ b≤truncatedDistance ξ c →
        truncatedDistance ξ a≤truncatedDistance ξ c))
    (fun a b => by simpa only [Bool.or_eq_true,decide_eq_true_eq] using le_total (truncatedDistance ξ a) (truncatedDistance ξ b))

theorem orderedRoots_nodup (p : ℤ[X]) (ξ : ℂ) (hi : Irreducible (p.map (Int.castRingHom ℚ))) :
    (orderedRoots p ξ).Nodup := by
  have he : (p.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)=p.map (Int.castRingHom ℂ) := by
    rw [map_map]; congr 1
  have hh := nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr hi.separable)
  rw [he,← orderedRoots_multiset p ξ] at hh
  exact hh

theorem positive_truncated_of_ne {ξ z : ℂ} (h : ξ≠z) : 0 < truncatedDistance ξ z :=
  lt_min zero_lt_one (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h)) (rootScale_pos _))

theorem rootScale_of_near {ξ z : ℂ} (h : truncatedDistance ξ z≤1/2) :
    rootScale z≤2*(1+‖ξ‖) ∧ ‖ξ-z‖≤2*(1+‖ξ‖)*truncatedDistance ξ z := by
  have hr : relativeDistance ξ z≤1/2 := (min_le_iff.mp h).resolve_left (by norm_num)
  have he : ‖ξ-z‖=truncatedDistance ξ z*rootScale z := by
    rw [truncatedDistance,min_eq_right (hr.trans (by norm_num)),relativeDistance,div_mul_cancel₀ _ (rootScale_pos _).ne']
  have hh := mul_le_mul_of_nonneg_right h (rootScale_pos z).le
  have htri : ‖z‖≤‖ξ-z‖+‖ξ‖ := by simpa only [dist_eq_norm,sub_zero,norm_sub_rev z ξ] using dist_triangle z ξ 0
  have hs : rootScale z≤2*(1+‖ξ‖) := by
    by_cases hb : ‖z‖≤1
    · rw [rootScale,max_eq_left hb]; linarith [norm_nonneg ξ]
    · rw [rootScale,max_eq_right (le_of_not_ge hb)] at he ⊢
      change truncatedDistance ξ z*rootScale z≤_ at hh
      rw [rootScale,max_eq_right (le_of_not_ge hb)] at hh
      linarith only [hh,he,htri]
  exact ⟨hs,by rw [he,mul_comm]; exact mul_le_mul_of_nonneg_right hs (truncatedDistance_nonneg _ _)⟩

theorem secondary_log_sum (p : ℤ[X]) (ξ : ℂ) (hi : Irreducible (p.map (Int.castRingHom ℚ))) (hd : p.natDegree≤3)
    (z : ℂ) (xs : List ℂ) (he : orderedRoots p ξ=z::xs) (hn : ∀ y∈xs, ξ≠y) :
    (xs.map (rootProximity ξ)).sum≤(p.natDegree-1 : ℕ)*log (measure p)+3*log (2*(1+‖ξ‖)) := by
  have hl := orderedRoots_length p ξ
  have hr := (orderedRoots_multiset p ξ).symm
  have hN := orderedRoots_nodup p ξ hi
  have hO := orderedRoots_pairwise p ξ
  rw [he] at hl hr hN hO
  let K := 2*(1+‖ξ‖)
  have hk : 0 < K := by dsimp [K]; positivity
  have hK : 0≤log K := log_nonneg (by dsimp [K]; linarith [norm_nonneg ξ])
  have hM : 0 < measure p := zero_lt_one.trans_le (one_le_measure (by intro hz; simp [hz] at hi))
  cases xs with
  | nil => simp only [List.length_cons,List.length_nil] at hl; simp [← hl,hK,K] at *
  | cons y ys =>
    have hy := positive_truncated_of_ne (hn y (by simp))
    cases ys with
    | nil =>
      have hdeg : p.natDegree=2 := by simpa using hl.symm
      have h := quadratic_secondary_distance p ((degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 2)).mpr hdeg)
        ξ z y (by simpa using hN) hr ((List.pairwise_cons.mp hO).1 y (by simp))
      have H := log_nonneg h
      change 0≤log (measure p*K*truncatedDistance ξ y) at H
      rw [log_mul (mul_pos hM hk).ne' hy.ne',log_mul hM.ne' hk.ne'] at H
      simp only [hdeg,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,rootProximity,
        show (2-1 : ℕ)=1 by decide,Nat.cast_one]
      change _≤(1:ℝ)*log (measure p)+3*log K
      linarith only [H,hK]
    | cons u us =>
      have hempty : us=[] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hl
        omega
      subst us
      have hdeg : p.natDegree=3 := by simpa using hl.symm
      have hu := positive_truncated_of_ne (hn u (by simp))
      simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or,List.nodup_nil,
        List.not_mem_nil,not_false_eq_true,and_true] at hN
      have ho := List.pairwise_cons.mp hO
      have H := log_nonneg (cubic_secondary_distances p
        ((degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 3)).mpr hdeg) ξ z y u hN.1.1 hN.1.2 hN.2 hr
        (ho.1 y (by simp)) ((List.pairwise_cons.mp ho.2).1 u (by simp)))
      change 0≤log ((measure p)^2*K^3*truncatedDistance ξ y*(truncatedDistance ξ u)^2) at H
      rw [log_mul (by positivity) (pow_ne_zero 2 hu.ne'),log_mul (by positivity) hy.ne',
        log_mul (by positivity) (by positivity),log_pow,log_pow,log_pow] at H
      norm_num only [Nat.cast_ofNat] at H
      simp only [hdeg,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,rootProximity]
      change _≤(2:ℝ)*log (measure p)+3*log K
      have H₀ := rootProximity_nonneg ξ u
      change 0≤ -log (truncatedDistance ξ u) at H₀
      linarith only [H,H₀]

end PiPolynomialValues
