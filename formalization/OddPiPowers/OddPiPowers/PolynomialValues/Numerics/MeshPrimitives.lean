module

public import OddPiPowers.PolynomialValues.Numerics.MeshLogIncrement
public import OddPiPowers.PolynomialValues.Analysis.LogPrimitives

/-! Each integer mesh record encloses both actual spatial primitives.
The common logarithmic offset uses the exact factorization of 20000. -/

@[expose] public section

namespace PiPolynomialValues

open Real

def meshOffsetLo : ℤ := -(13*((meshIncFloor 1 25 : ℤ)+27)+4*((meshIncFloor 4 13 : ℤ)+15))
def meshOffsetHi : ℤ := -(13*(meshIncFloor 1 25 : ℤ)+4*(meshIncFloor 4 13 : ℤ))

theorem meshOffset_bounds :
    (meshOffsetLo : ℝ) ≤ meshLogScale*(log 2-log 40000) ∧
      meshLogScale*(log 2-log 40000) ≤ (meshOffsetHi : ℝ) := by
  have H := mesh_inc_bounds (i := 1) (n := 25) (by decide) (by decide +kernel)
  have J := mesh_inc_bounds (i := 4) (n := 13) (by decide) (by decide +kernel)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one,Real.log_one,sub_zero] at H J
  have he : log 2-log 40000= -(13*log 2+4*(log 5-log 4)) := by
    have h : (40000 : ℝ) = 2^14*(5/4)^4 := by norm_num
    rw [h,Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,
      Real.log_div (by norm_num) (by norm_num)]
    ring
  rw [he]
  unfold meshOffsetLo meshOffsetHi
  push_cast
  constructor <;> linarith only [H.1,H.2,J.1,J.2]

def MeshLogState (i lo hi : ℕ) : Prop :=
  (lo : ℝ) ≤ meshLogScale*log (i : ℝ) ∧ meshLogScale*log (i : ℝ) ≤ (hi : ℝ)

theorem meshLogState_one : MeshLogState 1 0 0 := by simp [MeshLogState]

theorem MeshLogState.step {i lo hi n : ℕ} (hs : MeshLogState i lo hi) (hi' : 0 < i)
    (ht : 2*meshLogScale ≤ meshTermDen i n) :
    MeshLogState (i+1) (lo+meshIncFloor i n) (hi+meshIncFloor i n+n+2) := by
  have H := mesh_inc_bounds hi' ht
  dsimp [MeshLogState] at hs ⊢
  push_cast at H ⊢
  constructor <;> linarith only [hs.1,hs.2,H.1,H.2]

def meshPrimitivePass (i lo hi : ℕ) (f j : ℤ) : Bool := by
  let l := (lo : ℤ)+meshOffsetLo
  let u := (hi : ℤ)+meshOffsetHi
  let D : ℤ := 40000
  let S : ℤ := meshLogScale
  exact decide (f*D*S ≤ (i : ℤ)*10^9*(l-S) ∧ (i : ℤ)*10^9*(u-S) ≤ (f+2)*D*S ∧
    j*4*D^2*S ≤ (i : ℤ)^2*10^12*(2*l-3*S) ∧ (i : ℤ)^2*10^12*(2*u-3*S) ≤ (j+2)*4*D^2*S)

def MeshPrimitiveEnclosed (i : ℕ) (f j : ℤ) : Prop :=
  let x := (i : ℝ)/40000
  (f : ℝ) ≤ 10^9*logPrimitive x ∧ 10^9*logPrimitive x ≤ (f : ℝ)+2 ∧
    (j : ℝ) ≤ 10^12*energyPrimitive x ∧ 10^12*energyPrimitive x ≤ (j : ℝ)+2

theorem meshPrimitive_sound {i lo hi : ℕ} {f j : ℤ} (hi' : 0 < i)
    (hs : MeshLogState i lo hi) (hc : meshPrimitivePass i lo hi f j=true) :
    MeshPrimitiveEnclosed i f j := by
  let S := (meshLogScale : ℝ)
  let l := (lo : ℝ)+(meshOffsetLo : ℝ)
  let u := (hi : ℝ)+(meshOffsetHi : ℝ)
  let X := log (i : ℝ)+log 2-log 40000
  have hh : l ≤ S*X ∧ S*X ≤ u := by
    unfold l u X S
    constructor <;> linarith only [hs.1,hs.2,meshOffset_bounds.1,meshOffset_bounds.2]
  obtain ⟨ha,hb,hd,he⟩ := of_decide_eq_true hc
  have A : (f : ℝ)*40000*S ≤ (i : ℝ)*10^9*(l-S) := by dsimp [l,S]; exact_mod_cast ha
  have B : (i : ℝ)*10^9*(u-S) ≤ ((f : ℝ)+2)*40000*S := by dsimp [u,S]; exact_mod_cast hb
  have D : (j : ℝ)*4*40000^2*S ≤ (i : ℝ)^2*10^12*(2*l-3*S) := by dsimp [l,S]; exact_mod_cast hd
  have E : (i : ℝ)^2*10^12*(2*u-3*S) ≤ ((j : ℝ)+2)*4*40000^2*S := by dsimp [u,S]; exact_mod_cast he
  have hF : 10^9*logPrimitive ((i : ℝ)/40000) = (i : ℝ)*10^9*(X-1)/40000 := by
    unfold logPrimitive X
    rw [Real.log_div (Nat.cast_ne_zero.mpr hi'.ne') (by norm_num)]
    ring
  have hJ : 10^12*energyPrimitive ((i : ℝ)/40000) = (i : ℝ)^2*10^12*(2*X-3)/(4*40000^2) := by
    unfold energyPrimitive X
    rw [Real.log_div (Nat.cast_ne_zero.mpr hi'.ne') (by norm_num)]
    ring
  have hS : 0<S := by norm_num [S,meshLogScale]
  have hm : 0≤(i : ℝ)*10^9 := by positivity
  have hn : 0≤2*((i : ℝ)^2*10^12) := by positivity
  dsimp [MeshPrimitiveEnclosed]
  rw [hF,hJ]
  refine ⟨?_,?_,?_,?_⟩
  · apply (le_div_iff₀ (by norm_num)).mpr
    apply (le_of_mul_le_mul_right _ hS)
    linarith only [A,mul_le_mul_of_nonneg_left hh.1 hm]
  · apply (div_le_iff₀ (by norm_num)).mpr
    apply (le_of_mul_le_mul_right _ hS)
    linarith only [B,mul_le_mul_of_nonneg_left hh.2 hm]
  · apply (le_div_iff₀ (by norm_num)).mpr
    apply (le_of_mul_le_mul_right _ hS)
    linarith only [D,mul_le_mul_of_nonneg_left hh.1 hn]
  · apply (div_le_iff₀ (by norm_num)).mpr
    apply (le_of_mul_le_mul_right _ hS)
    linarith only [E,mul_le_mul_of_nonneg_left hh.2 hn]

end PiPolynomialValues
