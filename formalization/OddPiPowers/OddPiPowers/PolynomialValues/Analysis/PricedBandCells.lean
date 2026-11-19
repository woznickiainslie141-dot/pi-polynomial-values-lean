module

public import OddPiPowers.PolynomialValues.Analysis.BandIntegral

/-! Riemann sums on actual signed integer bands, allowing a different
continuous price test on each fixed cell and arbitrary jumps at its edges. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter
open scoped Topology

theorem sum_grid_blocks {A : Type*} [AddCommMonoid A] (F : ℕ → A) (B M : ℕ) :
    (∑ k ∈ range (B*M), F k) = ∑ l ∈ range B, ∑ k ∈ range M, F (l*M+k) := by
  induction B with
  | zero => simp
  | succ B ih => rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]

theorem actual_band_blocks (W M : ℕ) (F : ℤ → ℝ) :
    (∑ x : ↥(Icc (-((W*M : ℕ) : ℤ)) ((W*M : ℕ) : ℤ)), F x.val) =
      (∑ l ∈ range (2*W), ∑ k ∈ range M, F (((l : ℤ)-W)*M+k))+F ((W : ℤ)*M) := by
  let B := W*M
  rw [(Icc (-(B : ℤ)) (B : ℤ)).sum_coe_sort F,Int.Icc_eq_finset_map,sum_map]
  rw [show ((B : ℤ)+1-(-(B : ℤ))).toNat = 2*B+1 by omega,sum_range_succ]
  simp only [Function.Embedding.trans_apply,Nat.castEmbedding_apply,addLeftEmbedding_apply]
  rw [show 2*B=2*W*M by dsimp [B]; ring, sum_grid_blocks]
  congr 1
  · apply sum_congr rfl
    intro l _
    apply sum_congr rfl
    intro k _
    congr 1
    simp only [B,Nat.cast_mul,Nat.cast_add]
    ring
  · congr 1
    dsimp [B]
    push_cast
    ring

theorem priced_band_limit (D W : ℕ) (hD : 0<D) (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (F : ℤ → C(ℝ,ℝ)) :
    Tendsto (fun t => ((D*M t : ℕ) : ℝ)⁻¹*∑ x : ↥(Icc (-((W*M t : ℕ) : ℤ)) ((W*M t : ℕ) : ℤ)),
      F (x.val/(M t : ℤ)) ((x.val : ℝ)*((D*M t : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 (∑ l ∈ range (2*W), ∫ x in (((l : ℝ)-W)/D)..(((l : ℝ)+1-W)/D), F ((l : ℤ)-W) x)) := by
  let h (t : ℕ) := ((D*M t : ℕ) : ℝ)⁻¹
  have hp : (D : ℝ)≠0 := Nat.cast_ne_zero.mpr hD.ne'
  have he : ∀ᶠ t in atTop, 0<M t := hM.eventually (eventually_ge_atTop 1)
  have ht : Tendsto h atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (hM.const_mul_atTop' hD))
  have hstep : ∀ᶠ t in atTop, (M t : ℝ)*h t=(D : ℝ)⁻¹ := by
    filter_upwards [he] with t hm
    have hn : (M t : ℝ)≠0 := Nat.cast_ne_zero.mpr hm.ne'
    dsimp [h]
    push_cast
    field_simp
  have H (l : ℕ) := left_grid_integral_limit (F ((l : ℤ)-W)) (((l : ℝ)-W)/D) (((l : ℝ)+1-W)/D) M h
    (fun t => by dsimp [h]; positivity) ht (by apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg D); linarith)
    (hstep.mono fun t h => by rw [h]; field_simp; ring)
  have HB := (tendsto_finsetSum (range (2*W)) (fun l _ => H l)).add (ht.mul_const (F (W : ℤ) ((W : ℝ)/D)))
  simp only [zero_mul,add_zero] at HB
  apply HB.congr'
  filter_upwards [he,hstep] with t hm hs
  rw [actual_band_blocks W (M t) (fun x : ℤ => F (x/(M t : ℤ)) ((x : ℝ)*h t)),mul_add,mul_sum]
  congr 1
  · apply sum_congr rfl
    intro l _
    congr 1
    apply sum_congr rfl
    intro k hk
    have hm' : (M t : ℤ)≠0 := by exact_mod_cast hm.ne'
    have hk' : (k : ℤ)/(M t : ℤ)=0 := Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast mem_range.mp hk)
    have heq : (((l : ℤ)-W)*(M t : ℤ)+k)/(M t : ℤ)=(l : ℤ)-W := by
      rw [add_comm,Int.add_mul_ediv_right _ _ hm',hk',zero_add]
    simp only [heq,Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast]
    congr 1
    change ((l : ℝ)-W)/D+k*h t = (((l : ℝ)-W)*M t+k)*h t
    rw [add_mul,mul_assoc,hs,div_eq_mul_inv]
  · have hm' : (M t : ℤ)≠0 := by exact_mod_cast hm.ne'
    simp only [Int.mul_ediv_cancel _ hm',Int.cast_mul,Int.cast_natCast]
    change h t*F (W : ℤ) ((W : ℝ)/D) = h t*F (W : ℤ) (((W : ℝ)*M t)*h t)
    rw [mul_assoc,hs,div_eq_mul_inv]

end PiPolynomialValues.FourPeriod
