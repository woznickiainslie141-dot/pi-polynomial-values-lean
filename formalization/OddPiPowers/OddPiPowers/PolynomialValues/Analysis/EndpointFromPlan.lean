module

public import OddPiPowers.PolynomialValues.Analysis.ResultantRates

/-! An escaping sequence would give a selected integral polynomial
whose normalized logarithmic resultant has a strictly negative upper
bound. The primitive factor transfer then covers every nonzero input. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Finset Filter Polynomial Real
open scoped Topology

theorem EvaluationPlan.endpoint (P : EvaluationPlan) (hd3 : P.rates.degree≤3) (hw : 0≤P.rates.exponent)
    (hgap : 2*P.rates.Y<P.rates.target) : Endpoint π P.rates.degree (P.rates.exponent : ℝ) := by
  classical
  have hw' : 0≤(P.rates.exponent : ℝ) := by exact_mod_cast hw
  apply endpoint_of_no_escaping_input hw' (fun p hp hd => pi_cubic_value_ne_zero p hp (hd.trans hd3))
  intro p hall hh hsmall
  obtain ⟨k,hk,ψ,hψ,hdegree⟩ := fixed_degree_subsequence p hall
  let q i := p (ψ i)
  have hQ (i : ℕ) : PrimitiveInput P.rates.degree (q i) := hall (ψ i)
  have hY : (k : ℝ)≤(P.rates.Y : ℝ) := by
    have h : (k : ℝ)+1≤(P.rates.degree : ℝ) := by exact_mod_cast hk
    unfold RateData.Y
    push_cast
    linarith
  have hgap' := (Rat.cast_lt (K := ℝ)).mpr hgap
  have htarget : (P.rates.target : ℝ)=1+(P.rates.exponent : ℝ) := by simp [RateData.target]
  push_cast at hgap'
  have hcap : (k : ℝ)<1+(P.rates.exponent : ℝ) := by
    rw [← htarget]
    linarith only [hY,hgap',Nat.cast_nonneg (α := ℝ) k]
  have hheight : Tendsto (fun i => height (q i)) atTop atTop := hh.comp hψ.tendsto_atTop
  obtain ⟨b,hb,hsec,hmain,φ,hφ,H⟩ := primitive_root_budgets q hdegree hQ hd3 hheight hw' hcap (fun i => hsmall (ψ i))
  let f i := q (φ i)
  let hf (i : ℕ) : (f i).natDegree=k+1 := hdegree (φ i)
  let z (i : ℕ) := indexedRoot (f i) (π : ℂ) (hf i)
  let X (i : ℕ) := log (measure (f i))
  let y := ∑ j : Fin k, b j.succ
  have hX : Tendsto X atTop atTop := tendsto_log_atTop.comp
    ((measure_tendsto_of_height q (fun i => (hQ i).2.2.2) hheight).comp hφ.tendsto_atTop)
  have hne (i : ℕ) (z' : ℂ) (hz : z'∈((f i).map (Int.castRingHom ℂ)).roots) : (π : ℂ)≠z' := by
    have hp : f i≠0 := by intro h; have := (hQ (φ i)).2.2.1; change 0<(f i).natDegree at this; simp [h] at this
    exact pi_not_integer_root (f i) hp ((hQ (φ i)).2.2.2.trans hd3) hz
  have hn (i j) : (π : ℂ)≠z i j := hne i _ (indexed_root_mem _ _ _ j)
  have HC (j) : Tendsto (fun i => cappedProximity (1+(P.rates.exponent : ℝ)) (X i) π (z i j)) atTop (𝓝 (b j)) := H j
  have hM : (P.rates.target : ℝ)-y≤b 0 := by simpa only [htarget] using hmain
  have hprincipal : (k : ℝ)<b 0 := by
    change y≤k at hsec
    linarith only [hsec,hM,hY,hgap']
  have hreal := principal_real_eventually f hf hne X b HC (fun j =>
    (single_le_sum (s := univ) (f := fun j : Fin k => b j.succ) (fun j _ => (hb j.succ).1)
      (mem_univ j)).trans hsec |>.trans_lt hprincipal)
  let W := selectAtRoots P (fun i => z i 0) X hX
  let S := scaleAtRoots P (fun i => z i 0) X hX
  have hpos : 0<b 0 := (Nat.cast_nonneg k).trans_lt hprincipal
  have hnear := conjugate_taylor_decay hX (fun i => hn i 0) (HC 0) hpos le_rfl (half_pos hpos)
  have hroot : ∀ᶠ i in atTop, W.root i=z i 0 := by
    filter_upwards [hnear] with i h
    have hz : z i 0≠0 := by
      intro he
      have hnorm := h.1
      rw [he,norm_zero] at hnorm
      exact (not_le_of_gt (zero_lt_one : (0 : ℝ)<1)) hnorm
    change (if z i 0=0 then 1 else z i 0)=z i 0
    rw [if_neg hz]
  have hobs := real_root_resultant W f hf (fun i => (hQ (φ i)).2.1) hroot hreal
  exact S.resultant_rate_contradiction hk z b hn (fun j => (hb j).1) hsec hM HC hobs

end PiPolynomialValues
