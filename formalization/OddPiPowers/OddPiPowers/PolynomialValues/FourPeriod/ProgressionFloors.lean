module

public import OddPiPowers.PolynomialValues.FourPeriod.WeightedProduct
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! A consecutive prefix of a progression with invertible step contains
at least a full quotient of representatives of each prime-power residue. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

private theorem progression_first (M d : ℕ) (x : ℤ) (hM : 0 < M) (hc : d.Coprime M) :
    ∃ r : ℕ, r < M ∧ (M : ℤ) ∣ x-(d : ℤ)*r := by
  obtain ⟨u,v,hu⟩ := hc.isCoprime
  let b := u*x
  let r := (b%(M : ℤ)).toNat
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hr : (r : ℤ) = b%(M : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hM'.ne')
  refine ⟨r,?_,?_⟩
  · exact_mod_cast (hr.trans_lt (Int.emod_lt_of_pos _ hM'))
  · have hh : (M : ℤ) ∣ x-(d : ℤ)*b := by
      refine ⟨v*x,?_⟩
      dsimp [b]
      linear_combination -x * hu
    have hmod : (M : ℤ) ∣ b-(r : ℤ) := by rw [hr]; exact (Int.mod_modEq b M).dvd
    convert dvd_add hh (dvd_mul_of_dvd_right hmod (d : ℤ)) using 1 <;> ring

theorem progression_floor_le_card (M d m : ℕ) (x : ℤ) (hM : 0 < M) (hc : d.Coprime M) :
    m/M ≤ ((range m).filter (fun i : ℕ => (M : ℤ) ∣ x-(d : ℤ)*i)).card := by
  obtain ⟨r,hr,c,hc'⟩ := progression_first M d x hM hc
  let index (k : ℕ) := r+k*M
  have hi : Function.Injective index := by
    intro a b he
    exact Nat.eq_of_mul_eq_mul_right hM (Nat.add_left_cancel he)
  have hs : (range (m/M)).image index ⊆ (range m).filter (fun i => (M : ℤ) ∣ x-(d : ℤ)*i) := by
    intro i his
    obtain ⟨k,hkr,rfl⟩ := mem_image.mp his
    have hk' := Nat.mul_le_mul_right M (Nat.succ_le_of_lt (mem_range.mp hkr))
    rw [Nat.succ_mul] at hk'
    have hfloor := Nat.div_mul_le_self m M
    refine mem_filter.mpr ⟨mem_range.mpr (show r+k*M < m by omega),?_⟩
    refine ⟨c-(d : ℤ)*k,?_⟩
    simp only [index,Nat.cast_add,Nat.cast_mul]
    linear_combination hc'
  simpa only [card_image_of_injective _ hi,card_range] using card_le_card hs

def trackedPowers (p L : ℕ) (x : ℤ) : ℕ :=
  ∑ h ∈ range L, if (p : ℤ)^(h+1) ∣ x then 1 else 0

theorem trackedPowers_le (p L : ℕ) (x : ℤ) : trackedPowers p L x ≤ L := by
  simpa only [trackedPowers,Finset.sum_boole,card_range,Nat.cast_id] using
    (card_filter_le (range L) (fun h => (p : ℤ)^(h+1) ∣ x))

theorem trackedPowers_dvd (p L : ℕ) (x : ℤ) : (p : ℤ)^trackedPowers p L x ∣ x := by
  induction L with
  | zero => simp [trackedPowers]
  | succ L ih =>
    rw [trackedPowers,sum_range_succ]
    change (p : ℤ)^(trackedPowers p L x + _) ∣ x
    by_cases h : (p : ℤ)^(L+1) ∣ x
    · rw [if_pos h]
      exact (pow_dvd_pow _ (Nat.add_le_add_right (trackedPowers_le p L x) 1)).trans h
    · simpa only [if_neg h,add_zero] using ih

theorem factorial_le_tracked (p d m L : ℕ) (x : ℤ) (hp : p.Prime) (hc : d.Coprime p)
    (hL : p.log m ≤ L) :
    m.factorial.factorization p ≤ ∑ i ∈ range m, trackedPowers p L (x-(d : ℤ)*i) := by
  have he : m.factorial.factorization p = ∑ h ∈ range L, m / p^(h+1) := by
    rw [Nat.factorization_factorial hp (by omega : p.log m < L+1)]
    rw [Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  rw [he]
  unfold trackedPowers
  rw [sum_comm (s := range m)]
  apply sum_le_sum
  intro h _
  rw [Finset.sum_boole]
  have hh := progression_floor_le_card (p^(h+1)) d m x (pow_pos hp.pos _) (hc.pow_right _)
  simpa only [Nat.cast_pow,Nat.cast_id] using hh

end PiPolynomialValues.FourPeriod
