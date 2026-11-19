module

public import OddPiPowers.PolynomialValues.FourPeriod.ScaledColumns
public import OddPiPowers.PolynomialValues.FourPeriod.OriginPairs

/-! Quantify uniformly how far a bounded row deficit can change the
origin pair sum and the first two frequency thresholds. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

def scaledGain {V : ℕ} (a : Fin V → ℕ) (w z : ℕ) : ℕ :=
  ∑ v, ((a v - 2*z) + (a v - 2*z - 2*w))

theorem nodePairOrder_scaled_lower {V : ℕ} (node : Fin V → ℤ) (a m : Fin V → ℕ)
    (t K : ℕ) (hm : ∀ v, a v*t ≤ m v+K) :
    nodePairOrder node a * t ≤ nodePairOrder node m + V*V*K := by
  let S := (univ : Finset (Fin V)) ×ˢ (univ : Finset (Fin V))
  have hc : (∑ _p ∈ S, K) = V*V*K := by simp [S, nsmul_eq_mul]
  unfold nodePairOrder
  rw [sum_mul, ← hc, ← sum_add_distrib]
  apply sum_le_sum
  intro p _
  by_cases h : p.1 < p.2 ∧ node p.1 % 4 = node p.2 % 4
  · rw [if_pos h,if_pos h,← min_times_scale]
    have h₁ := hm p.1
    have h₂ := hm p.2
    omega
  · simp [h]

private theorem gain_thresholds (a m w z t K : ℕ) (hm : a*t ≤ m+K) :
    ((a-2*z)+(a-2*z-2*w))*t ≤
      (m-bandSize (z*t)) + (m-(bandSize (z*t)+bandSize (w*t))) + (2*K+3) := by
  rw [Nat.add_mul, Nat.sub_mul, Nat.sub_mul, Nat.sub_mul]
  simp only [bandSize, Nat.mul_assoc]
  omega

theorem prefix_quota_scaled_lower {V n : ℕ} (a m : Fin V → ℕ)
    (e : Fin n ≃ RowCandidates m) (w z t K : ℕ) (hm : ∀ v, a v*t ≤ m v+K) :
    (scaledGain a w z * t : ℕ) ≤ (∑ i, cutQuota (w*t) (z*t) (e i).2.val) +
      ((∑ v, m v : ℕ) : ℤ) + (V*(2*K+3) : ℕ) := by
  let quota (b : RowCandidates m) := cutQuota (w*t) (z*t) b.2.val
  change _ ≤ (∑ i, quota (e i)) + _ + _
  rw [Equiv.sum_comp e quota,Fintype.sum_sigma]
  have h (v : Fin V) : ((((a v-2*z)+(a v-2*z-2*w))*t : ℕ) : ℤ) ≤
      (∑ i : Fin (m v), quota ⟨v,i⟩) + (m v : ℤ) + ((2*K+3 : ℕ) : ℤ) := by
    have hb := cutQuota_prefix_sum_lower (m v) (w*t) (z*t)
    have hg := gain_thresholds (a v) (m v) w z t K (hm v)
    change _ ≤ (∑ i : Fin (m v), cutQuota (w*t) (z*t) i.val) + _ + _
    omega
  have hh := sum_le_sum (s := univ) (fun i _ => h i)
  unfold scaledGain
  rw [sum_mul, Nat.cast_sum]
  simpa only [Nat.cast_sum, sum_add_distrib, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul] using hh

end PiPolynomialValues.FourPeriod
