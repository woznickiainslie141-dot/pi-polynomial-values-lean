module

public import OddPiPowers.PolynomialValues.FourPeriod.PrimeAffineRate
public import OddPiPowers.PolynomialValues.Analysis.TailIntegral

/-! Prime sums in the direct scale y=p/N, including an empty interval
and the exact breakpoint of a positive-part affine function. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter MeasureTheory
open scoped Topology Interval

noncomputable def primeSlice (l r : ℝ) (N : ℕ) : Finset ℕ :=
  (Nat.primesLE ⌊r*N⌋₊).filter (fun p => l*N < (p : ℝ))

theorem mem_primeSlice (l r : ℝ) (hr : 0 ≤ r) (N p : ℕ) :
    p ∈ primeSlice l r N ↔ p.Prime ∧ l*N < (p : ℝ) ∧ (p : ℝ) ≤ r*N := by
  simp only [primeSlice,mem_filter,Nat.mem_primesLE,Nat.le_floor_iff (mul_nonneg hr (Nat.cast_nonneg _))]
  tauto

noncomputable def primeAverage (l r : ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ p ∈ primeSlice l r N, f ((p : ℝ)/N)*Real.log p)/N

theorem primeSlice_affine {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (a b : ℝ) :
    Tendsto (primeAverage l r (fun y => a+b*y)) atTop (𝓝 (∫ y in l..r, a+b*y)) := by
  rcases hlr.eq_or_lt with hr | hr
  · subst r
    have he (N : ℕ) : primeSlice l l N = ∅ := by
      ext p
      simp only [mem_primeSlice l l hl.le,notMem_empty,iff_false]
      rintro ⟨_,hx,hy⟩
      exact hx.not_ge hy
    rw [show primeAverage l l (fun y => a+b*y) = (fun _ : ℕ => (0 : ℝ)) by
      funext N; simp [primeAverage,he],intervalIntegral.integral_same]
    exact tendsto_const_nhds
  · let W : OddPiPowers.PrimeRates.PrimeWindow :=
      ⟨r⁻¹,l⁻¹,0,inv_pos.mpr (hl.trans hr), (inv_lt_inv₀ (hl.trans hr) hl).mpr hr⟩
    have he (N : ℕ) : primeSlice l r N = W.primes N := by
      ext p
      rw [mem_primeSlice l r (hl.trans hr).le,W.mem_primes]
      simp only [W,div_inv_eq_mul,mul_comm (N : ℝ)]
    have h := window_affine_tendsto W a b
    change Tendsto (fun N : ℕ => (∑ p ∈ primeSlice l r N, (a+b*((p : ℝ)/N))*Real.log p)/N) atTop _
    simpa only [he,integral_affine_real,W,inv_inv] using h

theorem primeSlice_ramp {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (a b : ℝ) (hb : 0 ≤ b) :
    Tendsto (primeAverage l r (fun y => max 0 (a-b*y))) atTop
      (𝓝 (∫ y in l..r, max 0 (a-b*y))) := by
  let f (y : ℝ) := max 0 (a-b*y)
  have hc : Continuous f := continuous_const.max (continuous_const.sub (continuous_const.mul continuous_id))
  have hlin : Continuous (fun y : ℝ => a-b*y) := continuous_const.sub (continuous_const.mul continuous_id)
  have hmem {p N : ℕ} (hN : 0 < N) (hp : p ∈ primeSlice l r N) :
      l ≤ (p : ℝ)/N ∧ (p : ℝ)/N ≤ r := by
    have hz := (mem_primeSlice _ _ (hl.le.trans hlr) _ _).mp hp
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    exact ⟨((lt_div_iff₀ hn).mpr hz.2.1).le,(div_le_iff₀ hn).mpr hz.2.2⟩
  have haff {s : ℝ} (hs : l ≤ s) :
      Tendsto (primeAverage l s (fun y => a-b*y)) atTop (𝓝 (∫ y in l..s, a-b*y)) := by
    simpa only [neg_mul,← sub_eq_add_neg] using primeSlice_affine hl hs a (-b)
  by_cases hz : a ≤ b*l
  · have he {x : ℝ} (hx : l ≤ x) : f x = 0 := max_eq_left (sub_nonpos.mpr (hz.trans (mul_le_mul_of_nonneg_left hx hb)))
    have hi : (∫ y in l..r, f y) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => 0) (fun y hy => he ((Set.uIcc_of_le hlr ▸ hy).1))]
      simp
    change Tendsto (primeAverage l r f) atTop (𝓝 (∫ y in l..r, f y))
    rw [hi]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    simp only [primeAverage]
    rw [sum_eq_zero (fun p hp => by rw [he (hmem hN hp).1,zero_mul]),zero_div]
  by_cases hr : b*r ≤ a
  · have he {x : ℝ} (hx : x ≤ r) : f x = a-b*x :=
      max_eq_right (sub_nonneg.mpr ((mul_le_mul_of_nonneg_left hx hb).trans hr))
    have hi : (∫ y in l..r, f y) = ∫ y in l..r, a-b*y :=
      intervalIntegral.integral_congr (fun y hy => he ((Set.uIcc_of_le hlr ▸ hy).2))
    change Tendsto (primeAverage l r f) atTop (𝓝 (∫ y in l..r, f y))
    rw [hi]
    apply (haff hlr).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    unfold primeAverage
    exact congrArg (fun v : ℝ => v/N) (sum_congr rfl (fun p hp => by rw [he (hmem hN hp).2]))
  · have hb' : 0 < b := by
      rcases hb.eq_or_lt with h|h
      · subst b; simp_all <;> linarith
      · exact h
    let s := a/b
    have hls : l < s := (lt_div_iff₀ hb').mpr (by linarith [not_le.mp hz,mul_comm l b])
    have hsr : s < r := (div_lt_iff₀ hb').mpr (by linarith [not_le.mp hr,mul_comm r b])
    have hleft {x : ℝ} (hx : x ≤ s) : f x = a-b*x := by
      apply max_eq_right
      have h := (le_div_iff₀ hb').mp hx
      linarith [mul_comm b x]
    have hright {x : ℝ} (hx : s ≤ x) : f x = 0 := by
      apply max_eq_left
      have h := (div_le_iff₀ hb').mp hx
      linarith [mul_comm b x]
    have hi : (∫ y in l..r, f y) = ∫ y in l..s, a-b*y := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := s) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
      rw [intervalIntegral.integral_congr (a := l) (b := s) (g := fun y => a-b*y)
        (fun y hy => hleft ((Set.uIcc_of_le hls.le ▸ hy).2)),
        intervalIntegral.integral_congr (a := s) (b := r) (g := fun _ => 0)
        (fun y hy => hright ((Set.uIcc_of_le hsr.le ▸ hy).1))]
      simp
    change Tendsto (primeAverage l r f) atTop (𝓝 (∫ y in l..r, f y))
    rw [hi]
    apply (haff hls.le).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hsub : primeSlice l s N ⊆ primeSlice l r N := by
      intro p hp
      have z := (mem_primeSlice _ _ (hl.trans hls).le _ _).mp hp
      exact (mem_primeSlice _ _ (hl.le.trans hlr) _ _).mpr
        ⟨z.1,z.2.1,z.2.2.trans (mul_le_mul_of_nonneg_right hsr.le hn.le)⟩
    unfold primeAverage
    apply congrArg (fun v : ℝ => v/N)
    calc
      _ = ∑ p ∈ primeSlice l s N, f ((p : ℝ)/N)*Real.log p := by
        apply sum_congr rfl
        intro p hp
        rw [hleft ((div_le_iff₀ hn).mpr ((mem_primeSlice _ _ (hl.trans hls).le _ _).mp hp).2.2)]
      _ = _ := by
        apply sum_subset hsub
        intro p hpr hps
        have z := (mem_primeSlice _ _ (hl.le.trans hlr) _ _).mp hpr
        have ht : s ≤ (p : ℝ)/N := by
          apply le_of_not_ge
          intro hh
          exact hps ((mem_primeSlice _ _ (hl.trans hls).le _ _).mpr ⟨z.1,z.2.1,(div_le_iff₀ hn).mp hh⟩)
        rw [hright ht,zero_mul]

end PiPolynomialValues.FourPeriod
