module

public import OddPiPowers.PolynomialValues.FourPeriod.FrequencyLoss
public import Mathlib.Data.Int.Interval

/-! An integral monic row of every prefix degree imposes the specified
extra frequency root exactly on the central subband. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

def fullBand (w : ℕ) : Finset ℤ := Icc (-(w : ℤ)) (w : ℤ)
def bandSize (w : ℕ) := 2*w+1

theorem card_fullBand (w : ℕ) : (fullBand w).card = bandSize w := by
  rw [fullBand, Int.card_Icc]
  unfold bandSize
  omega

theorem fullBand_mono {z w : ℕ} (hz : z ≤ w) : fullBand z ⊆ fullBand w := by
  intro t ht
  obtain ⟨hl,hr⟩ := mem_Icc.mp ht
  exact mem_Icc.mpr ⟨by omega,by omega⟩

def bandHit (z : ℕ) (t : ℤ) : ℕ := if t ∈ fullBand z then 1 else 0

def cutQuota (w z σ : ℕ) : ℤ :=
  if bandSize z ≤ σ then (((σ-bandSize z)/bandSize w : ℕ) : ℤ) else -1

def cutMultiplicity (w z σ : ℕ) (t : ℤ) : ℕ :=
  if bandSize z ≤ σ then (σ-bandSize z)/bandSize w + bandHit z t else 0

theorem cutMultiplicity_budget (w z σ : ℕ) (hz : z ≤ w) :
    ∑ t ∈ fullBand w, cutMultiplicity w z σ t ≤ σ := by
  by_cases he : bandSize z ≤ σ
  · simp only [cutMultiplicity, if_pos he, sum_add_distrib, sum_const, nsmul_eq_mul,
      card_fullBand, bandHit, Finset.sum_boole]
    have hf : (fullBand w).filter (fun t => t ∈ fullBand z) = fullBand z := by
      ext t
      exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨fullBand_mono hz h,h⟩⟩
    rw [hf, card_fullBand]
    change bandSize w * ((σ-bandSize z)/bandSize w) + bandSize z ≤ σ
    have hq := Nat.div_mul_le_self (σ-bandSize z) (bandSize w)
    rw [Nat.mul_comm] at hq
    omega
  · simp [cutMultiplicity,he]

theorem cutQuota_add_hit (w z σ : ℕ) (t : ℤ) :
    cutQuota w z σ + bandHit z t ≤ (cutMultiplicity w z σ t : ℤ) := by
  by_cases he : bandSize z ≤ σ
  · simp [cutQuota,cutMultiplicity,he]
  · by_cases ht : t ∈ fullBand z <;> simp [cutQuota,cutMultiplicity,he,bandHit,ht]

theorem raw_degree_cut {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ) (w z : ℕ) (hz : z ≤ w)
    (hs : ∀ j, (cols j).1 ∈ fullBand w)
    (hn : rawDeterminant (fun i => (node (e i).1, (e i).2.val)) cols ≠ 0) :
    ((rawDeterminant (fun i => (node (e i).1, (e i).2.val)) cols).natDegree : ℤ) +
      (∑ i, cutQuota w z (e i).2.val) + (∑ j, (bandHit z (cols j).1 : ℤ)) ≤
        ∑ j, ((cols j).2 : ℤ) :=
  raw_degree_frequency_loss e node cols _ hs (fun i => cutMultiplicity w z (e i).2.val)
    _ _ (fun i => cutMultiplicity_budget _ _ _ hz) (fun i j => cutQuota_add_hit _ _ _ _) hn

theorem cutQuota_lower (w z σ : ℕ) :
    -1 + (if bandSize z ≤ σ then 1 else 0) +
      (if bandSize z + bandSize w ≤ σ then 1 else 0) ≤ cutQuota w z σ := by
  by_cases h : bandSize z ≤ σ
  · rw [cutQuota,if_pos h, if_pos h]
    by_cases h' : bandSize z + bandSize w ≤ σ
    · rw [if_pos h']
      have hdiv : 1 ≤ (σ-bandSize z)/bandSize w :=
        (Nat.le_div_iff_mul_le (by unfold bandSize; omega)).mpr (by omega)
      omega
    · rw [if_neg h']
      exact Int.natCast_nonneg ((σ-bandSize z)/bandSize w)
  · have hh : ¬bandSize z + bandSize w ≤ σ := by omega
    simp [cutQuota,h,hh]

private theorem count_prefix_threshold (m k : ℕ) :
    (∑ i ∈ range m, if k ≤ i then (1 : ℤ) else 0) = ((m-k : ℕ) : ℤ) := by
  rw [Finset.sum_boole]
  have hs : (range m).filter (fun i => k ≤ i) = Ico k m := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico, and_comm]
  rw [hs, Nat.card_Ico]

theorem cutQuota_prefix_sum_lower (m w z : ℕ) :
    -(m : ℤ) + ((m-bandSize z : ℕ) : ℤ) + ((m-(bandSize z+bandSize w) : ℕ) : ℤ) ≤
      ∑ i : Fin m, cutQuota w z i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun s => cutQuota w z s)]
  have h := sum_le_sum (s := range m) (fun i _ => cutQuota_lower w z i)
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_neg, mul_one,
    count_prefix_threshold] at h
  exact h

end PiPolynomialValues.FourPeriod
