module

public import OddPiPowers.PolynomialValues.FourPeriod.OriginOrder
public import OddPiPowers.PolynomialValues.FourPeriod.PrimeLevels

/-! A row rank is charged after selecting any finite set of prime levels.
The charge remains monotone in the actual power of the argument. Thus
distinct exponents in each residue/order group can be replaced by 0,...,b-1. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

def levelsBelow (H : Finset ℕ) (a : ℕ) : ℕ := (H.filter (fun u => u < a)).card

def primeRankCharge (H : Finset ℕ) (a h : ℕ) : ℤ := (h : ℤ) - levelsBelow H (a+h)

private theorem levelsBelow_succ_le (H : Finset ℕ) (a : ℕ) : levelsBelow H (a+1) ≤ levelsBelow H a+1 := by
  have hs : H.filter (fun u => u < a+1) ⊆ insert a (H.filter (fun u => u < a)) := by
    intro u hu
    obtain ⟨hm,hl⟩ := mem_filter.mp hu
    by_cases he : u = a
    · exact mem_insert.mpr (Or.inl he)
    · exact mem_insert_of_mem (mem_filter.mpr ⟨hm,by omega⟩)
  exact (card_le_card hs).trans (card_insert_le _ _)

theorem primeRankCharge_mono (H : Finset ℕ) (a : ℕ) : Monotone (primeRankCharge H a) := by
  apply monotone_nat_of_le_succ
  intro h
  have hh := levelsBelow_succ_le H (a+h)
  unfold primeRankCharge
  rw [← Nat.add_assoc]
  omega

theorem levelsBelow_sub_le (H : Finset ℕ) (a b : ℕ) :
    (levelsBelow H b : ℤ) - levelsBelow H a ≤ ((b-a : ℕ) : ℤ) := by
  by_cases h : a ≤ b
  · have hh := primeRankCharge_mono H a (show 0 ≤ b-a from Nat.zero_le _)
    simp only [primeRankCharge,Nat.cast_zero,zero_sub,Nat.add_zero,Nat.add_sub_of_le h] at hh
    omega
  · have hs : H.filter (fun i => i < b) ⊆ H.filter (fun i => i < a) := by
      intro i hi
      obtain ⟨hb,hi'⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨hb,by omega⟩
    have hh : levelsBelow H b ≤ levelsBelow H a := card_le_card hs
    omega

theorem matched_level_charge (H : Finset ℕ) (a b j h : ℕ) (hab : b ≤ a) (hhj : h ≤ j) :
    ((min (j-h) (a-b) : ℕ) : ℤ) + primeRankCharge H a h + levelsBelow H (j+b) ≤ (j : ℤ) := by
  have h := levelsBelow_sub_le H (a+h) (j+b)
  unfold primeRankCharge
  omega

private theorem range_card_sum_le (S : Finset ℕ) (f : ℕ → ℤ) (hf : Monotone f) :
    (∑ i ∈ range S.card, f i) ≤ ∑ i ∈ S, f i := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hm ih =>
    have ha : a ∉ S := fun ha => (lt_irrefl a) (hm a ha)
    have he : S.card ≤ a := by
      simpa only [card_range] using card_le_card (show S ⊆ range a from fun i hi => mem_range.mpr (hm i hi))
    rw [card_insert_of_notMem ha,sum_range_succ,sum_insert ha,add_comm (f a)]
    exact add_le_add ih (hf he)

def groupedRankCharge {n : ℕ} (H : Finset ℕ) (p : ℕ) (rows : Fin n → ℤ × ℕ) : ℤ :=
  let tag := rowTag ∘ rows
  ∑ k ∈ univ.image tag, ∑ r ∈ range (univ.filter (fun i => tag i = k)).card,
    primeRankCharge H (k.2/p) r

theorem groupedRankCharge_le {n : ℕ} (H : Finset ℕ) (p : ℕ) (rows : Fin n → ℤ × ℕ)
    (h : Fin n → ℕ) (hi : Function.Injective (fun i => (rowTag (rows i),h i))) :
    groupedRankCharge H p rows ≤ ∑ i, primeRankCharge H ((rows i).2/p) (h i) := by
  let tag := rowTag ∘ rows
  let S (k : ℤ × ℕ) := univ.filter (fun i => tag i = k)
  calc
    _ ≤ ∑ k ∈ univ.image tag, ∑ i ∈ S k, primeRankCharge H (k.2/p) (h i) := by
      apply sum_le_sum
      intro k _
      have hinj : Set.InjOn h (S k) := fun a ha b hb he =>
        hi (Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) he)
      have hg := range_card_sum_le ((S k).image h) (primeRankCharge H (k.2/p)) (primeRankCharge_mono H _)
      rwa [card_image_of_injOn hinj,sum_image hinj] at hg
    _ = _ := by
      calc
        _ = ∑ k ∈ univ.image tag, ∑ i ∈ S k, primeRankCharge H ((rows i).2/p) (h i) := by
          apply sum_congr rfl
          intro k _
          apply sum_congr rfl
          intro i hi
          have htag : tag i = k := (mem_filter.mp hi).2
          have he := congrArg Prod.snd htag
          change (rows i).2 = k.2 at he
          rw [he]
        _ = _ := sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem tag hi) _

theorem groupedRankCharge_empty {n : ℕ} (p : ℕ) (rows : Fin n → ℤ × ℕ) :
    groupedRankCharge ∅ p rows = (originOrder rows : ℤ) := by
  have he (b : ℕ) : (∑ r ∈ range b, (r : ℤ)) = (b.choose 2 : ℕ) := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [sum_range_succ,ih,Nat.choose_succ_succ,Nat.choose_one_right,Nat.cast_add,add_comm]
  simp only [groupedRankCharge,originOrder,primeRankCharge,levelsBelow,filter_empty,card_empty,
    Nat.cast_zero,sub_zero,he,Nat.cast_sum]

end PiPolynomialValues.FourPeriod
