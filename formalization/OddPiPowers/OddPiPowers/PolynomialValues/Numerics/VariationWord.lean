module

public import OddPiPowers.PolynomialValues.Numerics.WideLane
public import OddPiPowers.PolynomialValues.Numerics.ReferenceCell

/-! A single scalar product sums the largest absolute jump at every edge,
using the already checked packed rows. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

theorem SpatialLane.jump_abs_le (v : SpatialLane) (i : ℕ) : |v.jump i|≤2^31 := by
  have h := Nat.mod_lt (v.data/(2^32)^i) (by decide : 0 < 2^32)
  change |((v.data/(2^32)^i%(2^32) : ℕ) : ℤ)-2^31|≤2^31
  rw [abs_le]
  omega

def absoluteLane (v : SpatialLane) := 2*packedPositive 127 641 v.packed-v.packed

theorem absoluteLane_eq (v : SpatialLane) (h : v.passes=true) : absoluteLane v=packedSum spatialBase 641 (fun i => |v.jump i|) := by
  have hword := (v.sound h).1.trans (packEval_eq _ _ _)
  have hp : packedPositive 127 641 (packedSum spatialBase 641 v.jump)=
      packedSum spatialBase 641 (fun i => max 0 (v.jump i)) := by
    apply packedPositive_sound 127 641 v.jump
    intro i _
    have hh := abs_le.mp (v.jump_abs_le i)
    constructor <;> omega
  rw [absoluteLane,hword,hp,← packedSum_scale,← packedSum_sub]
  apply packedSum_congr
  intro i _
  rw [abs_eq_max_neg]
  omega

def variationWord (rows : List SpatialLane) :=
  rows.foldr (fun v z => packedMax 127 641 (absoluteLane v) z) 0

theorem variation_word_sound (rows : List SpatialLane) (h : ∀ v∈rows, v.passes=true) :
    variationWord rows=packedSum spatialBase 641 (variationAt rows) ∧ ∀ i, |variationAt rows i|≤2^31 := by
  induction rows with
  | nil =>
    constructor
    · simp [variationWord,variationAt,maxWithFloor,packedSum]
    · intro i; change |(0:ℤ)|≤2^31; decide
  | cons v vs ih =>
    obtain ⟨he,hm⟩ := ih (fun w hw => h _ (List.mem_cons_of_mem _ hw))
    have H (i : ℕ) : variationAt (v::vs) i=max |v.jump i| (variationAt vs i) := rfl
    constructor
    · change packedMax 127 641 (absoluteLane v) (variationWord vs)=_
      rw [he,absoluteLane_eq _ (h _ (by simp))]
      apply packedMax_sound 127 641 (fun i => |v.jump i|) (variationAt vs)
      intro i _
      have ha := v.jump_abs_le i
      have h₀ := abs_nonneg (v.jump i)
      have hb := abs_le.mp (hm i)
      constructor <;> omega
    · intro i
      rw [abs_of_nonneg (variationAt_nonneg _ _),H]
      exact max_le (v.jump_abs_le i) (abs_le.mp (hm i)).2

def fastVariation (rows : List SpatialLane) := laneDot (variationWord rows)

theorem fastVariation_sound (rows : List SpatialLane) (h : ∀ v∈rows, v.passes=true) : fastVariation rows=referenceVariation rows := by
  obtain ⟨he,hm⟩ := variation_word_sound rows h
  rw [fastVariation,he,laneDot_eq _ (fun i _ => hm i),referenceVariation,packEval_one]

end PiPolynomialValues
