module

public import OddPiPowers.PolynomialValues.FourPeriod.PrimeCutDenominator

/-! Express the signed prime budget as a sum of individual row and column
tail counts. Any fixed injection of node ranks bounds the row tails above. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

def rowLevelCount {n : ℕ} (rows : Fin n → ℤ × ℕ) (p h : ℕ) : ℕ :=
  let tag := rowTag ∘ rows
  ∑ k ∈ univ.image tag, ((univ.filter (fun i => tag i = k)).card - (h - k.2/p))

def columnLevelCount {n J : ℕ} {U : Fin J → ℕ} (d : Fin n ≃ Column U) (p h : ℕ) : ℕ :=
  (univ.filter (fun i => h ≤ (d i).1.val+columnOrder (d i)/p)).card

private theorem sum_levels (H : Finset ℕ) (a : ℕ) :
    (levelsBelow H a : ℤ) = ∑ u ∈ H, if u < a then (1 : ℤ) else 0 := by simp [levelsBelow]

private theorem sum_prefix_levels (H : Finset ℕ) (a b : ℕ) :
    (∑ r ∈ range b, (levelsBelow H (a+r) : ℤ)) = ∑ u ∈ H, ((b-(u+1-a) : ℕ) : ℤ) := by
  simp only [sum_levels]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  have he : (range b).filter (fun r => u < a+r) = Ico (u+1-a) b := by
    ext r
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  simp only [sum_boole,he,Nat.card_Ico]

theorem primeLevelBudget_counts {n J : ℕ} {U : Fin J → ℕ} (rows : Fin n → ℤ × ℕ)
    (d : Fin n ≃ Column U) (p : ℕ) (H : Finset ℕ) :
    primeLevelBudget rows d p H =
      (∑ j, ((d j).1.val : ℤ)) - originOrder rows +
      ∑ u ∈ H, ((rowLevelCount rows p (u+1) : ℤ) - columnLevelCount d p (u+1)) := by
  let tag := rowTag ∘ rows
  let S (k : ℤ × ℕ) := univ.filter (fun i => tag i = k)
  have h₀ := groupedRankCharge_empty p rows
  simp only [groupedRankCharge,primeRankCharge,levelsBelow,filter_empty,card_empty,Nat.cast_zero,sub_zero] at h₀
  have hr : groupedRankCharge H p rows =
      (originOrder rows : ℤ) - ∑ u ∈ H, (rowLevelCount rows p (u+1) : ℤ) := by
    simp only [groupedRankCharge,primeRankCharge,sum_sub_distrib,h₀,sum_prefix_levels]
    congr 1
    rw [sum_comm]
    simp only [rowLevelCount,Nat.cast_sum]
  have hc : (∑ j, (levelsBelow H ((d j).1.val + columnOrder (d j)/p) : ℤ)) =
      ∑ u ∈ H, (columnLevelCount d p (u+1) : ℤ) := by
    simp only [sum_levels]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    simp only [sum_boole,columnLevelCount,Nat.succ_le_iff]
  rw [primeLevelBudget,hr,hc,sum_sub_distrib]
  ring

theorem rowLevelCount_le_rank {n : ℕ} (rows : Fin n → ℤ × ℕ) (rank : Fin n → ℕ)
    (hi : Function.Injective (fun i => (rowTag (rows i),rank i))) (p h : ℕ) :
    rowLevelCount rows p h ≤ ∑ i, if h ≤ (rows i).2/p+rank i then 1 else 0 := by
  classical
  let tag := rowTag ∘ rows
  let S (k : ℤ × ℕ) := univ.filter (fun i => tag i = k)
  let F (i : Fin n) : ℕ := if h ≤ (rows i).2/p+rank i then 1 else 0
  change _ ≤ ∑ i, F i
  rw [← sum_fiberwise_of_maps_to (t := univ.image tag) (fun i hi => mem_image_of_mem tag hi) F]
  change (∑ k ∈ univ.image tag, ((S k).card-(h-k.2/p))) ≤ _
  apply sum_le_sum
  intro k _
  let q := h-k.2/p
  have hs : (S k).card - q ≤ ((S k).filter (fun i => q ≤ rank i)).card := by
    let T := (S k).filter (fun i => rank i < q)
    have hsmall : T.card ≤ q := by
      rw [← card_range q]
      apply card_le_card_of_injOn rank
      · intro i hi'
        exact mem_range.mpr (mem_filter.mp hi').2
      · intro i hai j haj hq
        exact hi (Prod.ext ((mem_filter.mp (mem_filter.mp hai).1).2.trans
          (mem_filter.mp (mem_filter.mp haj).1).2.symm) hq)
    have ht := card_filter_add_card_filter_not (s := S k) (fun i => rank i < q)
    simp only [not_lt] at ht
    change ((S k).filter (fun i => rank i < q)).card ≤ q at hsmall
    omega
  apply hs.trans_eq
  change _ = ∑ i ∈ S k, F i
  simp only [F,sum_boole,Nat.cast_id]
  apply congrArg Finset.card
  ext i
  simp only [mem_filter]
  constructor <;> rintro ⟨hs,ht⟩
  · have he := congrArg Prod.snd ((mem_filter.mp hs).2)
    change (rows i).2 = k.2 at he
    exact ⟨hs,by rw [he]; dsimp [q] at ht; omega⟩
  · have he := congrArg Prod.snd ((mem_filter.mp hs).2)
    change (rows i).2 = k.2 at he
    rw [he] at ht
    exact ⟨hs,by dsimp [q]; omega⟩

end PiPolynomialValues.FourPeriod
