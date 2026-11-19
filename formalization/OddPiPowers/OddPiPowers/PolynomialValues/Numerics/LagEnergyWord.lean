module

public import OddPiPowers.PolynomialValues.Numerics.EnergyLag
public import OddPiPowers.PolynomialValues.Numerics.PackedDot
public import OddPiPowers.PolynomialValues.Numerics.PackedBitwise

/-! The signed quadratic correction is evaluated one lag at a time by
integer multiplication. Opposite orientations are combined before
rounding the second primitive upwards. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def energyBase : ℤ := 2^192
def energyBias : ℤ := 2^191

def lagWord (n : ℕ) (x rev : ℤ) :=
  packedWindow energyBase (x*rev+energyBias*packedOnes energyBase (n+n)) n n-
    energyBias*packedOnes energyBase n

def lagEnergyWord (n : ℕ) (x rev jrev sign : ℤ) :=
  let c := (2*sign)*lagWord n x rev
  packedDot energyBase energyBias n c jrev+
    2*packedDot energyBase energyBias n (packedPositive 191 n c) (packedOnes energyBase n)

theorem lagWord_sound {n : ℕ} (hn : 0<n) (a : ℕ → ℤ) (h₁ : ∀ i<n, |a i|≤10^13)
    (h₂ : ∑ j ∈ range n, |a (n-1-j)|≤10^13)
    {x rev : ℤ} (hx : x=packEval energyBase n a) (hr : rev=packEval energyBase n (fun j => a (n-1-j))) :
    lagWord n x rev=packedSum energyBase n (positiveLag n a) := by
  have H (k : ℕ) : |meshConvolution n n a (fun j => a (n-1-j)) k| ≤ 10^13*10^13 :=
    (meshConvolution_abs (by decide) h₁ k).trans (mul_le_mul_of_nonneg_left h₂ (by decide))
  rw [lagWord,hx,hr,packed_product_window hn hn (by decide : 1<energyBase) a _ energyBias n n le_rfl
    (fun k _ => by have hh := abs_le.mp (H k); unfold energyBias energyBase; constructor <;> omega)]
  exact congrArg (packedSum energyBase n) (funext (fun k => positiveLag_convolution n a k))

theorem lagEnergyWord_sound {n : ℕ} (hn : 0<n) (hN : n≤80001) (a J : ℕ → ℤ) (sign : ℤ)
    (hs : |sign|≤1) (h₁ : ∀ i<n, |a i|≤10^13) (h₂ : ∑ j ∈ range n, |a (n-1-j)|≤10^13)
    (hJ : ∀ i<n, |J i|≤10^17)
    {x rev wj : ℤ} (hx : x=packEval energyBase n a) (hr : rev=packEval energyBase n (fun j => a (n-1-j)))
    (hj : wj=packEval energyBase n (fun j => J (n-1-j))) :
    lagEnergyWord n x rev wj sign =
      ∑ k ∈ range n, ((2*sign)*positiveLag n a k*J k+2*max 0 ((2*sign)*positiveLag n a k)) := by
  let c (k : ℕ) := (2*sign)*positiveLag n a k
  let p (k : ℕ) := max 0 (c k)
  have h (k : ℕ) : |c k|≤2*10^26 := by
    have H := meshConvolution_abs (n := n) (by decide : (0:ℤ)≤10^13) h₁ (c := fun j => a (n-1-j)) (n+k)
    rw [positiveLag_convolution] at H
    have H' := H.trans (mul_le_mul_of_nonneg_left h₂ (by decide : (0:ℤ)≤10^13))
    unfold c
    rw [abs_mul,abs_mul]
    calc
      _ ≤ (2*1)*(10^13*10^13) := mul_le_mul (by simpa using mul_le_mul_of_nonneg_left hs (by decide : (0:ℤ)≤2))
        H' (abs_nonneg _) (by decide)
      _ = _ := by decide
  have hp (k : ℕ) : |p k|≤2*10^26 := by
    have H := abs_le.mp (h k)
    rw [show p k=max 0 (c k) from rfl,abs_of_nonneg (le_max_left (0:ℤ) (c k))]
    omega
  have hsum (f : ℕ → ℤ) (hf : ∀ k, |f k|≤2*10^26) : ∑ k ∈ range n, |f k|≤80001*(2*10^26) := by
    apply (sum_le_sum (s := range n) (fun k _ => hf k)).trans
    simp only [sum_const,card_range,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (by decide)
  have hwpos : packedPositive 191 n (packedSum energyBase n c)=packedSum energyBase n p :=
    packedPositive_sound _ _ c (fun i _ => by have H := abs_le.mp (h i); constructor <;> omega)
  have ho : packedOnes energyBase n=packEval energyBase n (fun _ => 1) := by
    rw [packEval_eq,packedOnes_eq (by decide : 1<energyBase)]
  rw [lagEnergyWord,lagWord_sound hn _ h₁ h₂ hx hr,← packedSum_scale]
  change packedDot energyBase energyBias n (packedSum energyBase n c) wj+
    2*packedDot energyBase energyBias n (packedPositive 191 n (packedSum energyBase n c)) (packedOnes energyBase n)=_
  rw [hj,hwpos,ho,packedDot_sound (by decide : 1<energyBase) hn c J (by decide) hJ (hsum c h)
    (by decide : (10^17 : ℤ)*(80001*(2*10^26))≤energyBias) (by decide : (10^17 : ℤ)*(80001*(2*10^26))+energyBias<energyBase)]
  rw [packedDot_sound (by decide : 1<energyBase) hn p (fun _ => 1) (by decide : (0:ℤ)≤1)
    (fun _ _ => by decide) (hsum p hp) (by decide) (by decide),mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  dsimp [c,p]
  ring

end PiPolynomialValues
