module

public import OddPiPowers.PolynomialValues.Numerics.SpatialLane
public import OddPiPowers.PolynomialValues.Numerics.PackedDot
public import OddPiPowers.PolynomialValues.Numerics.PackedBitwise

/-! Decode each 32-bit density word on a balanced tree. A dot product and
a wordwise positive part determine the total jump and total variation. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

theorem meshWord_skip (b d j k : ℕ) : meshWord b (d/b^k) j=meshWord b d (k+j) := by
  simp only [meshWord,Nat.div_div_eq_div_mul,pow_add]

def wideTree : ℕ → ℕ → ℤ
  | 0,d => (meshWord (2^32) d 0 : ℤ)
  | k+1,d =>
    let m := 2^k
    wideTree k d+wideTree k (d/(2^32)^m)*spatialBase^m

theorem wideTree_eq (k d : ℕ) : wideTree k d=packedSum spatialBase (2^k) (fun j => (meshWord (2^32) d j : ℤ)) := by
  induction k generalizing d with
  | zero => simp [wideTree,packedSum]
  | succ k ih =>
    rw [wideTree,ih,ih,show 2^(k+1)=2^k+2^k by rw [pow_succ]; omega,packedSum_append]
    simp only [meshWord_skip]

def wide641 (d : ℕ) :=
  wideTree 9 d+(wideTree 7 (d/(2^32)^512)+(meshWord (2^32) d 640 : ℤ)*spatialBase^128)*spatialBase^512-
    (2^31)*packedOnes spatialBase 641

theorem wide641_eq (d : ℕ) : wide641 d=packEval spatialBase 641 (meshFWord d) := by
  let f (j : ℕ) : ℤ := meshWord (2^32) d j
  have he : packedSum spatialBase 641 f=wideTree 9 d+
      (wideTree 7 (d/(2^32)^512)+f 640*spatialBase^128)*spatialBase^512 := by
    rw [show 641=512+(128+1) by decide,packedSum_append,packedSum_append,wideTree_eq,wideTree_eq]
    simp only [meshWord_skip]
    have h : packedSum spatialBase 1 (fun i => f (512+(128+i)))=f 640 := by simp [packedSum]
    rw [h]
    rfl
  rw [wide641,packEval_eq]
  change _=packedSum spatialBase 641 (fun j => f j-2^31)
  rw [packedSum_sub,← he,packedSum_const (by decide : 1<spatialBase)]

def laneDot (word : ℤ) := packedDot spatialBase spatialBias 641 word (packedOnes spatialBase 641)

theorem laneDot_eq (a : ℕ → ℤ) (ha : ∀ i < 641, |a i|≤2^31) :
    laneDot (packedSum spatialBase 641 a)=∑ i ∈ range 641, a i := by
  have h : (∑ i ∈ range 641, |a i|)≤641*2^31 := by
    simpa using sum_le_sum (s := range 641) (fun i hi => ha i (mem_range.mp hi))
  have hw : packedOnes spatialBase 641=packEval spatialBase 641 (fun _ => 1) := by
    rw [packEval_eq,packedOnes_eq (by decide : 1<spatialBase)]
  rw [laneDot,hw]
  simpa only [one_mul] using packedDot_sound (b := spatialBase) (bias := spatialBias) (by decide)
    (by decide : 0 < 641) a (fun _ => 1) (by decide : (0:ℤ)≤1) (fun _ _ => by decide) h (by decide) (by decide)

def SpatialLane.wideCheck (v : SpatialLane) : Bool :=
  decide (v.packed=wide641 v.data ∧ laneDot v.packed=0 ∧ v.norm=2*laneDot (packedPositive 127 641 v.packed) ∧
    v.norm≤10^12 ∧ |v.slope|≤10^8 ∧ |v.β|≤10^8)

theorem SpatialLane.wideCheck_sound (v : SpatialLane) (hv : v.wideCheck=true) : v.passes=true := by
  obtain ⟨he,hzero,hvabs,hn,hs,hb⟩ := of_decide_eq_true hv
  have he' : v.packed=packEval spatialBase 641 v.jump := he.trans (wide641_eq v.data)
  have hword := he'.trans (packEval_eq _ _ _)
  have h (i : ℕ) : |v.jump i|≤2^31 := by
    have ht := Nat.mod_lt (v.data/(2^32)^i) (by decide : 0 < 2^32)
    change |((v.data/(2^32)^i%(2^32) : ℕ) : ℤ)-2^31|≤2^31
    rw [abs_le]
    omega
  rw [hword,laneDot_eq _ (fun i _ => h i)] at hzero
  let pos (j : ℕ) := max 0 (v.jump j)
  have hp : packedPositive 127 641 v.packed=packedSum spatialBase 641 pos := by
    rw [hword]
    apply packedPositive_sound
    intro i _
    have hh := abs_le.mp (h i)
    constructor <;> omega
  have hp' (i : ℕ) : |pos i|≤2^31 := by
    rw [abs_of_nonneg (le_max_left 0 _)]
    exact max_le (by decide) (abs_le.mp (h i)).2
  rw [hp,laneDot_eq _ (fun i _ => hp' i)] at hvabs
  have hA (j : ℕ) : |v.jump j|=2*pos j-v.jump j := by dsimp [pos]; rw [abs_eq_max_neg]; omega
  apply decide_eq_true
  refine ⟨he',by simpa only [packEval_one] using hzero,?_,hn,hs,hb⟩
  rw [packEval_one]
  simp only [hA,sum_sub_distrib,← mul_sum,hzero,sub_zero]
  exact hvabs

theorem wideCheck_rows (rows : List SpatialLane) (h : rows.all SpatialLane.wideCheck=true) :
    rows.all SpatialLane.passes=true := List.all_eq_true.mpr (fun v hv => v.wideCheck_sound (List.all_eq_true.mp h v hv))

end PiPolynomialValues
