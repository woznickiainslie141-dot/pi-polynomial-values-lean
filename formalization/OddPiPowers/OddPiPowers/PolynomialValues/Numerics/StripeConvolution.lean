module

public import OddPiPowers.PolynomialValues.Numerics.PackedWindows
public import OddPiPowers.PolynomialValues.Numerics.SignedMeshSamples

/-! The 125 residue classes of the interpolation mesh. For each
position of the full grid the window gives the actual signed
sum of all 641 density jumps times their primitive values. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def spatialBase : ℤ := 2^128
def spatialBias : ℤ := 2^127
def stripeSize (r : ℕ) := if r=0 then 1281 else 1280
def stripeCount (r : ℕ) := if r=0 then 641 else 640

def stripeSample (r j : ℕ) : ℤ := signedMeshF ((r : ℤ)+125*j-80000)+2^31

structure StripeBasis (r : ℕ) where
  word : ℤ
  checked : word=packEval spatialBase (stripeSize r) (stripeSample r)

def stripePotential (r : ℕ) (packedF packedD : ℤ) : ℤ :=
  packedWindow spatialBase (packedF*packedD+spatialBias*packedOnes spatialBase (stripeSize r+641)) 640 (stripeCount r)-
    spatialBias*packedOnes spatialBase (stripeCount r)

def fieldSample (r k : ℕ) (d : ℕ → ℤ) : ℤ :=
  ∑ j ∈ range 641, signedMeshF ((r : ℤ)+125*k-125*j)*d j

theorem stripeSample_range {r j : ℕ} (hr : r<125) (hj : j<stripeSize r) :
    |stripeSample r j|≤2^32 := by
  have h : ((r : ℤ)+125*j-80000).natAbs≤80000 := by
    by_cases h : r=0
    · simp [stripeSize,h] at hj
      omega
    · simp [stripeSize,h] at hj
      omega
  have H := abs_le.mp (signedMeshF_range _ h)
  rw [stripeSample,abs_le]
  constructor <;> omega

theorem stripePotential_sound {r : ℕ} (hr : r<125) (d : ℕ → ℤ)
    (hzero : ∑ j ∈ range 641, d j=0) (hsize : ∑ j ∈ range 641, |d j|≤10^12)
    {pf pd : ℤ} (hf : pf=packEval spatialBase (stripeSize r) (stripeSample r))
    (hd : pd=packEval spatialBase 641 d) :
    stripePotential r pf pd=packedSum spatialBase (stripeCount r) (fun k => fieldSample r k d) := by
  have hm : 0<stripeSize r := by unfold stripeSize; split <;> decide
  have hs : 640+stripeCount r≤stripeSize r+641 := by unfold stripeSize stripeCount; split <;> decide
  have hu : ∀ j<stripeSize r+641, 0≤meshConvolution (stripeSize r) 641 (stripeSample r) d j+spatialBias ∧
      meshConvolution (stripeSize r) 641 (stripeSample r) d j+spatialBias<spatialBase := by
    intro j _
    have H := (meshConvolution_abs (a := stripeSample r) (by decide : (0 : ℤ)≤2^32)
      (fun i hi => stripeSample_range hr (j := i) hi) (c := d) j).trans
      (mul_le_mul_of_nonneg_left hsize (by decide : (0 : ℤ)≤2^32))
    have HH := abs_le.mp H
    unfold spatialBase spatialBias
    constructor <;> omega
  rw [stripePotential,hf,hd,packed_product_window hm (by decide) (by decide : 1<spatialBase)
    (stripeSample r) d spatialBias 640 (stripeCount r) hs hu]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  have hm' : 640+k<stripeSize r := by
    by_cases h : r=0 <;> simp [stripeSize,stripeCount,h] at hk' ⊢ <;> omega
  dsimp only
  apply congrArg (fun z : ℤ => z*spatialBase^k)
  rw [meshConvolution_interior (n := 641) (by omega) hm']
  have he (j : ℕ) (hj : j∈range 641) :
      stripeSample r (640+k-j)*d j=signedMeshF ((r : ℤ)+125*k-125*j)*d j+(2:ℤ)^31*d j := by
    have hsub : j≤640+k := by have := mem_range.mp hj; omega
    unfold stripeSample
    rw [Nat.cast_sub hsub,Nat.cast_add,Nat.cast_ofNat,
      show (r:ℤ)+125*(640+(k:ℤ)-j)-80000=r+125*k-125*j by ring,add_mul]
  rw [sum_congr rfl he,sum_add_distrib,← mul_sum,hzero,mul_zero,add_zero]
  rfl

def fieldWord (r : ℕ) (potential β slope norm : ℤ) : ℤ :=
  40000*(potential+(-β*10^9+2*norm)*packedOnes spatialBase (stripeCount r))+
    10^9*slope*(((r : ℤ)-40000)*packedOnes spatialBase (stripeCount r)+
      125*packEval spatialBase (stripeCount r) (fun k => (k : ℤ)))

theorem fieldWord_sound (r : ℕ) (d : ℕ → ℤ) (β slope norm : ℤ)
    {p : ℤ} (hp : p=packedSum spatialBase (stripeCount r) (fun k => fieldSample r k d)) :
    fieldWord r p β slope norm=packedSum spatialBase (stripeCount r)
      (fun k => 40000*(fieldSample r k d+(-β*10^9+2*norm))+10^9*slope*(((r : ℤ)-40000)+125*k)) := by
  rw [fieldWord,hp,packEval_eq,packedSum_add,packedSum_scale,packedSum_add,packedSum_const (by decide : 1<spatialBase),
    packedSum_scale,packedSum_add,packedSum_const (by decide : 1<spatialBase),packedSum_scale]

end PiPolynomialValues
