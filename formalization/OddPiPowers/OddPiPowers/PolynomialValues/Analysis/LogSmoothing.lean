module

public import OddPiPowers.PolynomialValues.Analysis.RadialChordError

/-! Uniform integral error when the real logarithmic singularity is
smoothed inside an interval. Its endpoint expression tends to zero. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory Set Filter intervalIntegral
open scoped Topology Interval

noncomputable def logSmoothingMass (q : ℝ) :=
  2*((2+q)*log (2+q)-q*log q-2*log 2)

theorem logSmoothingMass_tendsto : Tendsto logSmoothingMass (𝓝 0) (𝓝 0) := by
  have hc : Continuous logSmoothingMass := by
    unfold logSmoothingMass
    fun_prop
  simpa [logSmoothingMass] using hc.tendsto 0

theorem logSmoothing_integrable {q : ℝ} (hq : 0 < q) (a b : ℝ) :
    IntervalIntegrable (logSmoothing q) volume a b := by
  have hc : Continuous fun s : ℝ => log (|s|+q) :=
    (continuous_abs.add_const q).log (fun s => (add_pos_of_nonneg_of_pos (abs_nonneg _) hq).ne')
  have hh : IntervalIntegrable (fun s : ℝ => log |s|) volume a b := by
    simpa only [log_abs] using (intervalIntegrable_log' (a := a) (b := b))
  exact (hc.intervalIntegrable _ _).sub hh

theorem integral_logSmoothing {q : ℝ} (hq : 0 < q) :
    (∫ s in (-2 : ℝ)..2, logSmoothing q s) = logSmoothingMass q := by
  have h₂ : (∫ s in (0 : ℝ)..2, logSmoothing q s) = (2+q)*log (2+q)-q*log q-2*log 2 := by
    have he : (∫ s in (0 : ℝ)..2, logSmoothing q s) =
        ∫ s in (0 : ℝ)..2, (log (s+q)-log s) := by
      apply integral_congr
      intro s hs
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hs
      simp [logSmoothing,abs_of_nonneg hs.1]
    have hi : IntervalIntegrable (fun t : ℝ => log (t+q)) volume 0 2 :=
      (IntervalIntegrable.comp_add_right_iff (f := log) (c := q) (by finiteness)).mpr intervalIntegrable_log'
    rw [he,integral_sub hi
      intervalIntegrable_log',integral_comp_add_right,integral_log,integral_log]
    simp
    ring
  have hneg : (∫ s in (-2 : ℝ)..0, logSmoothing q s) =
      ∫ s in (0 : ℝ)..2, logSmoothing q s := by
    have h := integral_comp_neg (a := (0 : ℝ)) (b := 2) (logSmoothing q)
    simpa only [neg_zero,logSmoothing,abs_neg] using h.symm
  rw [← integral_add_adjacent_intervals (logSmoothing_integrable hq (-2) 0)
    (logSmoothing_integrable hq 0 2),hneg,h₂,logSmoothingMass]
  ring

theorem integral_logSmoothing_le {q a b x : ℝ} (hq : 0 < q) (ha : -1 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) (hx : x ∈ Icc (-1 : ℝ) 1) :
    (∫ t in a..b, logSmoothing q (t-x)) ≤ logSmoothingMass q := by
  rw [integral_comp_sub_right,← integral_logSmoothing hq]
  apply integral_mono_interval (by linarith [hx.2]) (by linarith) (by linarith [hx.1]) _
    (logSmoothing_integrable hq (-2) 2)
  apply ae_restrict_of_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with s hs
  exact sub_nonneg.mpr (log_le_log (abs_pos.mpr hs) (by linarith))

end PiPolynomialValues
