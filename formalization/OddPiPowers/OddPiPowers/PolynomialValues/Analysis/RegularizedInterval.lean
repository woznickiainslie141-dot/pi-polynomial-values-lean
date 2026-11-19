module

public import OddPiPowers.PolynomialValues.Analysis.LogSmoothing
public import OddPiPowers.PolynomialValues.Analysis.IntervalCharge

/-! The potentials of actual interval densities converge uniformly, with
an explicit bound independent of the test frequency. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory Set Filter intervalIntegral
open scoped Topology Interval

noncomputable def intervalPotential (a b : ℝ) : C(FrequencyInterval,ℝ) :=
  ⟨fun x => logPrimitive (b-x)-logPrimitive (a-x),
    (logPrimitive_continuous.comp (continuous_const.sub continuous_subtype_val)).sub
      (logPrimitive_continuous.comp (continuous_const.sub continuous_subtype_val))⟩

theorem projected_frequency {a b t : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) (ht : t ∈ Icc a b) :
    (frequencyProjection t : ℝ) = t := by
  have hz : t ∈ Icc (-1 : ℝ) 1 := ⟨ha.trans ht.1,ht.2.trans hb⟩
  change (Set.projIcc (-1 : ℝ) 1 (by norm_num) t : ℝ) = t
  rw [Set.projIcc_of_mem _ hz]

theorem intervalPotential_error {a b r : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hr : 0 < r) (hr1 : r < 1) (x : FrequencyInterval) :
    let D := radialPotential unitFrequency r (intervalCharge frequencyProjection a b) x-intervalPotential a b x
    (b-a)*log r ≤ D ∧ D ≤ logSmoothingMass (2*(1-r)) := by
  let q := 2*(1-r)
  have hq : 0 < q := by dsimp [q]; positivity
  let K (t : ℝ) := log (radialPair r (unitFrequency (frequencyProjection t)) (unitFrequency x))
  let L (t : ℝ) := frequencyLog (t-x)
  let S (t : ℝ) := logSmoothing q (t-x)
  have hK : IntervalIntegrable K volume a b := by
    have he : K = fun t => radialPotential unitFrequency r (ContinuousMap.evalCLM ℝ x) (frequencyProjection t) :=
      funext fun t => (radialPotential_point _ unitFrequency_norm hr.le hr1 _ _).symm
    rw [he]
    exact ((radialPotential _ _ _).continuous.comp frequencyProjection.continuous).intervalIntegrable _ _
  have hL : IntervalIntegrable L volume a b := by
    simpa [L] using (intervalIntegrable_frequencyLog (a-x) (b-x)).comp_sub_right (x : ℝ)
  have hS : IntervalIntegrable S volume a b := by
    simpa [S] using (logSmoothing_integrable hq (a-x) (b-x)).comp_sub_right (x : ℝ)
  have he : ∀ᵐ t ∂volume.restrict (Icc a b), log r ≤ K t-L t ∧ K t-L t ≤ S t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (x : ℝ))] with t ht hne
    have hreal : (unitFrequency (frequencyProjection t)).re = t :=
      (unitFrequency_re _).trans (projected_frequency ha hb ht)
    have hh := radial_log_error (unitFrequency_norm (frequencyProjection t)) (unitFrequency_norm x)
      (by rwa [hreal,unitFrequency_re]) hr hr1
    simpa only [hreal,unitFrequency_re] using hh
  have lo := integral_mono_ae_restrict hab (f := fun _ : ℝ => log r) intervalIntegrable_const
    (hK.sub hL) (he.mono fun t ht => ht.1)
  have hi := integral_mono_ae_restrict hab (hK.sub hL) hS (he.mono fun t ht => ht.2)
  have hv : (∫ t in a..b, L t) = intervalPotential a b x := by
    change (∫ t in a..b, frequencyLog (t-x)) = _
    rw [integral_comp_sub_right,integral_frequencyLog]
    rfl
  have hk : (∫ t in a..b, K t) = radialPotential unitFrequency r (intervalCharge frequencyProjection a b) x :=
    (radialPotential_interval unitFrequency unitFrequency_norm hr.le hr1 _ _ _ x).symm
  rw [intervalIntegral.integral_const,smul_eq_mul,intervalIntegral.integral_sub hK hL,hv,hk] at lo
  rw [intervalIntegral.integral_sub hK hL,hv,hk] at hi
  exact ⟨lo,hi.trans (integral_logSmoothing_le hq ha hab hb x.2)⟩

theorem intervalPotential_limit {ι : Type*} {F : Filter ι} {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (hr1 : ∀ i, r i < 1) (ht : Tendsto r F (𝓝 1))
    {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun i => radialPotential unitFrequency (r i) (intervalCharge frequencyProjection a b)) F
      (𝓝 (intervalPotential a b)) := by
  have hq : Tendsto (fun i => 2*(1-r i)) F (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub ht).const_mul 2
  have he : Tendsto (fun i => |(b-a)*log (r i)|+|logSmoothingMass (2*(1-r i))|) F (𝓝 0) := by
    simpa using (((ht.log one_ne_zero).const_mul (b-a)).abs.add (logSmoothingMass_tendsto.comp hq).abs)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ he
  intro i
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  obtain ⟨hl,hh⟩ := intervalPotential_error ha hab hb (hr i) (hr1 i) x
  change |radialPotential unitFrequency (r i) (intervalCharge frequencyProjection a b) x - intervalPotential a b x| ≤ _
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le ((b-a)*log (r i)),abs_nonneg (logSmoothingMass (2*(1-r i)))]
  · linarith [le_abs_self (logSmoothingMass (2*(1-r i))),abs_nonneg ((b-a)*log (r i))]

end PiPolynomialValues
