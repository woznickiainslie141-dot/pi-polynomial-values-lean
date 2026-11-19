module

public import OddPiPowers.PolynomialValues.Analysis.BandIntegral
public import OddPiPowers.PolynomialValues.Analysis.TailIntegral

/-! A threshold bounds the moment of every tail of an actual allocation.
The limiting excess integral on each frequency band is explicit. -/

@[expose] public section

namespace PiPolynomialValues

open Finset MeasureTheory

theorem finite_tail_moment {ι : Type*} [Fintype ι] (s : Finset ι) (x : ι → ℝ) (q : ℝ) :
    (∑ i ∈ s, x i) ≤ (s.card : ℝ)*q+∑ i, max 0 (x i-q) := by
  have hg := sum_le_sum (s := s) (fun i _ => show x i≤q+max 0 (x i-q) by linarith [le_max_right 0 (x i-q)])
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at hg
  exact hg.trans (add_le_add_right (sum_le_sum_of_subset_of_nonneg (subset_univ s)
    (fun i _ _ => le_max_left 0 (x i-q))) _)

theorem band_excess_integral {q w : ℝ} (hq : 0≤q) (hw : 0≤w) :
    (∫ x in -w..w, max 0 (x-q))=(max 0 (w-q))^2/2 := by
  have hz (a b : ℝ) (hab : a≤b) (hb : b≤q) :
      (∫ x in a..b, max 0 (x-q))=0 := by
    calc
      _ = ∫ _ in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hab] at hx
        exact max_eq_left (sub_nonpos.mpr (hx.2.trans hb))
      _ = 0 := by simp
  by_cases h : w≤q
  · rw [hz (-w) w (by linarith) h,max_eq_left (sub_nonpos.mpr h)]
    norm_num
  have hwq := le_of_not_ge h
  have H : (∫ x in q..w, max 0 (x-q))=(w-q)^2/2 := by
    calc
      _ = ∫ x in q..w, -q+1*x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hwq] at hx
        change max 0 (x-q) = _
        rw [max_eq_right (sub_nonneg.mpr hx.1)]
        ring
      _ = _ := by rw [integral_affine_real]; ring
  have C : Continuous (fun x : ℝ => max 0 (x-q)) := continuous_const.max (continuous_id.sub continuous_const)
  rw [← intervalIntegral.integral_add_adjacent_intervals (C.intervalIntegrable (-w) q) (C.intervalIntegrable q w),
    hz (-w) q (by linarith) le_rfl,H,max_eq_right (sub_nonneg.mpr hwq),zero_add]

theorem threshold_band_moment {q w : ℝ} (hq : 0≤q) (hw : 0≤w) :
    q*max 0 (w-q)+(∫ x in -w..w, max 0 (x-q)) = max 0 (w^2-q^2)/2 := by
  rw [band_excess_integral hq hw]
  rcases le_total w q with h|h
  · rw [max_eq_left (sub_nonpos.mpr h),max_eq_left (sub_nonpos.mpr (pow_le_pow_left₀ hw h 2))]
    ring
  · rw [max_eq_right (sub_nonneg.mpr h),max_eq_right (sub_nonneg.mpr (pow_le_pow_left₀ hq h 2))]
    ring

end PiPolynomialValues
