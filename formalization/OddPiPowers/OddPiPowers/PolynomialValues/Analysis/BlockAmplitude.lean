module

public import OddPiPowers.PolynomialValues.Analysis.BlockScale
public import OddPiPowers.PolynomialValues.Analysis.CenteredAllocation

/-! Exponential upper bounds for a whole allocated block. All bounded
column factors are paid separately from the linear field and the
regularized logarithmic interaction. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Real Filter
open scoped Topology

theorem pairEnvelope_pos {m : ℕ} (x : Fin m → ℤ) : 0<pairEnvelope x :=
  prod_pos (fun _ _ => by positivity)

theorem separated_block_bound {m : ℕ} (hm : 0<m) (x : Fin m → ℤ) (y : Fin m → FrequencyInterval)
    {N r : ℝ} (hN : 2≤N) (hr : 0<r) (hr1 : r<1) (hx : ∀ i, (x i : ℝ)=N*(y i : ℝ))
    (A B T : Fin m → ℝ) (ha : ∀ i, 0≤A i) (hb : ∀ i, 0≤B i) (ht : ∀ i, A i*B i≤exp (T i)) :
    factorialWeight m*(∏ i, A i)*(pairEnvelope x*∏ i, B i)≤
      exp (N^2*(blockScaleCost N r m+radialInteraction unitFrequency r (atomicCharge y (fun _ => N⁻¹))
        (atomicCharge y (fun _ => N⁻¹))/2)+∑ i, T i) := by
  let Q := blockScaleCost N r m+radialInteraction unitFrequency r (atomicCharge y (fun _ => N⁻¹))
    (atomicCharge y (fun _ => N⁻¹))/2
  have hfreq := (div_le_iff₀ (by positivity : 0<N^2)).mp (block_scale_bound hm x y hN hr hr1 hx)
  have hh : factorialWeight m*pairEnvelope x≤exp (N^2*Q) := by
    rw [← exp_log ((factorialWeight_pos m).trans_le le_rfl) ,← exp_log (pairEnvelope_pos x),← exp_add]
    exact exp_le_exp.mpr (by change _≤N^2*Q; rw [mul_comm (N^2)]; exact hfreq)
  have ht' : (∏ i, A i)*(∏ i, B i)≤exp (∑ i, T i) := by
    rw [← prod_mul_distrib,Real.exp_sum]
    exact prod_le_prod₀ (fun i _ => mul_nonneg (ha i) (hb i)) (fun i _ => ht i)
  rw [Real.exp_add,mul_mul_mul_comm]
  exact mul_le_mul hh ht' (mul_nonneg (prod_nonneg fun i _ => ha i) (prod_nonneg fun i _ => hb i)) (exp_pos _).le

theorem bounded_power_exp {x B : ℝ} {j J : ℕ} (hx : 0≤x) (hB : 1≤B) (h : x≤B) (hj : j≤J) :
    x^j≤exp ((J : ℝ)*log B) := by
  rw [exp_nat_mul,exp_log (zero_lt_one.trans_le hB)]
  exact (pow_le_pow_left₀ hx h j).trans (pow_le_pow_right₀ hB hj)

noncomputable def columnOverhead (K : ℝ) (n J : ℕ) :=
  (J : ℝ)*(log 2+log K+log (K+(n : ℝ)^2+1))

theorem blockGrowth_le {m n : ℕ} (hm : m≤n) : (blockGrowth m : ℝ)≤(n : ℝ)^2+1 := by
  have h := frequencyPairs_twice_card m
  have hsq : (m : ℝ)^2≤(n : ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m)
    (Nat.cast_le.mpr hm) 2
  simp only [blockGrowth,Nat.cast_add,Nat.cast_one]
  linarith only [h,hsq,Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) (frequencyPairs m).card]

theorem center_column_bound {m n j h J : ℕ} (hm : m≤n) (hj : j≤J) (hh : h≤j) (v t a : ℤ) (p : ℂ)
    {K : ℝ} (hK : 1≤K) (hv : ‖(v : ℂ)-(a : ℂ)‖≤K) (hp : ‖p‖≤K) :
    ‖centerAmplitude v t a j h p‖*(‖p‖+blockGrowth m)^(j-h)≤
      exp ((t : ℝ)*p.re+columnOverhead K n J) := by
  have h₂ := bounded_power_exp (by norm_num : (0:ℝ)≤2) (by norm_num : (1:ℝ)≤2) le_rfl hj
  have hd := bounded_power_exp (norm_nonneg _) hK hv (hh.trans hj)
  have hG := blockGrowth_le hm
  have hb := bounded_power_exp (show 0≤‖p‖+(blockGrowth m : ℝ) by positivity)
    (show 1≤K+(n : ℝ)^2+1 by linarith [sq_nonneg (n : ℝ)])
    (by linarith only [hp,hG] : ‖p‖+blockGrowth m≤K+(n : ℝ)^2+1) (Nat.sub_le j h |>.trans hj)
  have hc : ‖centerAmplitude v t a j h p‖ =
      2^j*‖(v : ℂ)-(a : ℂ)‖^h*exp ((t : ℝ)*p.re) := by
    simp [centerAmplitude,norm_mul,norm_pow,Complex.norm_exp,Complex.mul_re]
  rw [hc]
  calc
    _ ≤ (exp ((J:ℝ)*log 2)*exp ((J:ℝ)*log K)*exp ((t:ℝ)*p.re))*exp ((J:ℝ)*log (K+(n:ℝ)^2+1)) := by
      apply mul_le_mul _ hb (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul h₂ hd (by positivity) (by positivity)) (exp_pos _).le
    _ = _ := by simp only [← exp_add]; congr 1; unfold columnOverhead; ring

end PiPolynomialValues.FourPeriod
