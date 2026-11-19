module

public import OddPiPowers.PolynomialValues.Analysis.EmpiricalPairBound
public import OddPiPowers.PolynomialValues.Analysis.FactorialPrefixSize

/-! Cancellation of the frequency scale with the row factorials.
The diagonal and factorial errors vanish for every selected sequence
whose row mass has its prescribed positive limit. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter Real
open scoped Topology

theorem frequencyPairs_twice_card (m : ℕ) :
    2*((frequencyPairs m).card : ℝ)+(m : ℝ)=(m : ℝ)^2 := by
  have H := sum_frequencyPairs_symm (n := m) (fun _ _ => (1 : ℝ)) (fun _ _ => rfl)
  simpa [sq] using H.symm

noncomputable def blockScaleCost (N r m : ℝ) : ℝ :=
  (m/N)^2/2*(3/2-log (2*(m/N))+log (1/r+(4/N)/(1-r)^2))+
    (m/N)*((1+log (m+1)-log (1-r))/N)

theorem block_scale_bound {m : ℕ} (hm : 0<m) (x : Fin m → ℤ) (y : Fin m → FrequencyInterval)
    {N r : ℝ} (hN : 2≤N) (hr : 0<r) (hr1 : r<1) (hx : ∀ i, (x i : ℝ)=N*(y i : ℝ)) :
    let μ := atomicCharge y (fun _ => N⁻¹)
    (log (factorialWeight m)+log (pairEnvelope x))/N^2 ≤
      blockScaleCost N r m+radialInteraction unitFrequency r μ μ/2 := by
  intro μ
  let c := 1/r+(4/N)/(1-r)^2
  have hN' : 0<N := by linarith
  have hm' : 0<(m : ℝ) := by exact_mod_cast hm
  have hcl : 1≤c := le_trans ((le_div_iff₀ hr).mpr (by linarith)) (le_add_of_nonneg_right (by positivity))
  have hs : 0≤log (N/2)+log c := add_nonneg (log_nonneg (by linarith)) (log_nonneg hcl)
  have hp := frequencyPairs_twice_card m
  have he : ((frequencyPairs m).card : ℝ)≤(m : ℝ)^2/2 := by linarith
  have H := empirical_pair_bound x y hN' hr hr1 hx
  change log (pairEnvelope x) ≤ ((frequencyPairs m).card : ℝ)*(log (N/2)+log c)+
    (N^2*radialInteraction unitFrequency r μ μ-(m : ℝ)*(2*log (1-r)))/2 at H
  have HF := log_factorialWeight_upper m
  have hh : log (2*((m : ℝ)/N))=log (m : ℝ)-log (N/2) := by
    rw [show 2*((m : ℝ)/N)=(m : ℝ)/(N/2) by ring,log_div hm'.ne' (by positivity)]
  rw [div_le_iff₀ (sq_pos_of_pos hN'),blockScaleCost,hh]
  change _≤(((_ : ℝ)/N)^2/2*(3/2-(log (m : ℝ)-log (N/2))+log c)+
    ((m : ℝ)/N)*((1+log ((m : ℝ)+1)-log (1-r))/N)+_)*N^2
  field_simp [hN'.ne']
  unfold factorialPrimitive at HF
  nlinarith only [HF,H,mul_le_mul_of_nonneg_right he hs]

theorem blockScaleCost_limit {ι : Type*} {l : Filter ι} {N m : ι → ℝ} {a r : ℝ}
    (hN : Tendsto N l atTop) (hm : Tendsto (fun i => m i/N i) l (𝓝 a)) (ha : 0<a)
    (hpos : ∀ i, 0≤m i) (hr : 0<r) :
    Tendsto (fun i => blockScaleCost (N i) r (m i)) l (𝓝 (a^2/2*(3/2-log (2*a)+log (1/r)))) := by
  have hinv : Tendsto (fun i => (N i)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hN
  have hf : Tendsto (fun i => (m i+1)/N i) l (𝓝 a) := by
    simpa only [add_div,one_div,add_zero] using hm.add hinv
  have hlog : Tendsto (fun i => log ((m i+1)/N i)) l (𝓝 (log a)) :=
    (Real.continuousAt_log ha.ne').tendsto.comp hf
  have hslow : Tendsto (fun i => log (N i)/N i) l (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hN
  have hsmall : Tendsto (fun i => log (m i+1)/N i) l (𝓝 0) := by
    have H := (hlog.mul hinv).add hslow
    simp only [mul_zero,zero_add] at H
    apply H.congr'
    filter_upwards [hN.eventually (eventually_gt_atTop 0)] with i hi
    have hp : m i+1>0 := by linarith [hpos i]
    rw [log_div hp.ne' hi.ne']
    ring
  have he : Tendsto (fun i => (1+log (m i+1)-log (1-r))/N i) l (𝓝 0) := by
    simpa only [div_eq_mul_inv,sub_mul,add_mul,one_mul,mul_zero,add_zero,sub_zero] using
      (hinv.add hsmall).sub (hinv.const_mul (log (1-r)))
  have hc : Tendsto (fun i => 1/r+(4/N i)/(1-r)^2) l (𝓝 (1/r)) := by
    simpa only [div_eq_mul_inv,mul_zero,zero_mul,add_zero] using
      ((hinv.const_mul 4).mul_const ((1-r)^2)⁻¹).const_add (1/r)
  have h₁ := (Real.continuousAt_log (by positivity : 2*a≠0)).tendsto.comp (hm.const_mul 2)
  have h₂ := (Real.continuousAt_log (by positivity : 1/r≠0)).tendsto.comp hc
  simpa only [blockScaleCost,mul_zero,add_zero,Function.comp_apply] using
    (((hm.pow 2).div_const 2).mul ((h₁.const_sub (3/2)).add h₂)).add (hm.mul he)

end PiPolynomialValues.FourPeriod
