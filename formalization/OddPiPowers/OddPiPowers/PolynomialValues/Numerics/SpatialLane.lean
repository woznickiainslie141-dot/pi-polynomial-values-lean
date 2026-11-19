module

public import OddPiPowers.PolynomialValues.Numerics.StripeConvolution

/-! One reference node stores the signed density jumps, affine price,
and an exact word for its jump polynomial. Every accepted field uses
the same jumps in the integer calculation and the real potential. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

structure SpatialLane where
  data : ℕ
  packed : ℤ
  norm : ℤ
  slope : ℤ
  β : ℤ

def SpatialLane.jump (v : SpatialLane) (j : ℕ) := meshFWord v.data j

def SpatialLane.passes (v : SpatialLane) : Bool :=
  decide (v.packed=packEval spatialBase 641 v.jump ∧ packEval 1 641 v.jump=0 ∧
    v.norm=packEval 1 641 (fun j => |v.jump j|) ∧ v.norm≤10^12 ∧ |v.slope|≤10^8 ∧ |v.β|≤10^8)

theorem packEval_one (n : ℕ) (a : ℕ → ℤ) : packEval 1 n a=∑ i ∈ range n, a i := by
  simp [packEval_eq,packedSum]

theorem SpatialLane.sound (v : SpatialLane) (hv : v.passes=true) :
    v.packed=packEval spatialBase 641 v.jump ∧ (∑ j ∈ range 641, v.jump j)=0 ∧
    v.norm=(∑ j ∈ range 641, |v.jump j|) ∧ v.norm≤10^12 ∧ |v.slope|≤10^8 ∧ |v.β|≤10^8 := by
  simpa only [passes,decide_eq_true_eq,packEval_one] using hv

def SpatialLane.sample (v : SpatialLane) (r k : ℕ) :=
  40000*(fieldSample r k v.jump+(-v.β*10^9+2*v.norm))+10^9*v.slope*((r : ℤ)-40000+125*k)

def SpatialLane.word (v : SpatialLane) (r : ℕ) (basis : StripeBasis r) :=
  fieldWord r (stripePotential r basis.word v.packed) v.β v.slope v.norm

theorem SpatialLane.word_sound (v : SpatialLane) (hv : v.passes=true) {r : ℕ} (hr : r<125) (basis : StripeBasis r) :
    v.word r basis=packedSum spatialBase (stripeCount r) (v.sample r) := by
  obtain ⟨h₁,h₂,h₃,h₄,_,_⟩ := v.sound hv
  exact fieldWord_sound r v.jump v.β v.slope v.norm (stripePotential_sound hr v.jump h₂ (h₃.symm.trans_le h₄) basis.checked h₁)

theorem stripe_node_bound {r k : ℕ} (hr : r<125) (hk : k<stripeCount r) : r+125*k≤80000 := by
  by_cases h : r=0 <;> simp [stripeCount,h] at hk ⊢ <;> omega

theorem SpatialLane.sample_range (v : SpatialLane) (hv : v.passes=true) {r k : ℕ} (hr : r<125)
    (hk : k<stripeCount r) : |v.sample r k|≤10^27 := by
  obtain ⟨_,_,h₃,h₄,hs,hb⟩ := v.sound hv
  have h := stripe_node_bound hr hk
  have H : |fieldSample r k v.jump|≤2^31*v.norm := by
    rw [h₃,mul_sum,fieldSample]
    apply (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
    intro j hj
    have hj' := mem_range.mp hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (signedMeshF_range _ (by omega)) (abs_nonneg _)
  have hn : 0≤v.norm := by rw [h₃]; exact sum_nonneg fun _ _ => abs_nonneg _
  have hq : |(r : ℤ)-40000+125*k|≤40000 := by rw [abs_le]; omega
  have ht := mul_le_mul hs hq (abs_nonneg _) (by decide : (0 : ℤ)≤10^8)
  rw [← abs_mul] at ht
  have hp := abs_le.mp ht
  have hg := abs_le.mp H
  have hβ := abs_le.mp hb
  rw [sample,abs_le]
  constructor <;> nlinarith only [hp.1,hp.2,hg.1,hg.2,h₄,hn,hβ.1,hβ.2]

noncomputable def SpatialLane.realField (v : SpatialLane) (x : ℝ) :=
  ((v.slope : ℝ)*x-(v.β : ℝ)+
    ∑ j ∈ range 641, (v.jump j : ℝ)*logPrimitive (x+1-125*j/40000))/100000

theorem SpatialLane.sample_upper (v : SpatialLane) (hv : v.passes=true) {r k : ℕ}
    (hr : r<125) (hk : k<stripeCount r) :
    v.realField (((r : ℝ)+125*k)/40000-1) ≤ (v.sample r k : ℝ)/(40000*100000*10^9) := by
  let i : ℤ := (r : ℤ)+125*k
  have hi := stripe_node_bound hr hk
  have H := mesh_field_sample_upper i (fun j : Fin 641 => 125*(j.val : ℤ)) (fun j => v.jump j.val)
    (fun j => by have hh := j.isLt; dsimp [i]; omega)
  let R (j : ℕ) := (v.jump j : ℝ)*(10^9*logPrimitive (((i-125*(j : ℤ) : ℤ) : ℝ)/40000))
  let Z (j : ℕ) := v.jump j*signedMeshF (i-125*(j : ℤ))+2*|v.jump j|
  change (∑ j : Fin 641, R j.val)≤((∑ j : Fin 641, Z j.val : ℤ) : ℝ) at H
  rw [Fin.sum_univ_eq_sum_range R 641,Fin.sum_univ_eq_sum_range Z 641] at H
  dsimp only [i,R,Z] at H
  push_cast at H
  obtain ⟨_,_,hn,_,_,_⟩ := v.sound hv
  have hsum : (∑ j ∈ range 641, (v.jump j : ℝ)*(10^9*logPrimitive (((r : ℝ)+125*k-125*j)/40000))) ≤
      (fieldSample r k v.jump : ℝ)+2*v.norm := by
    rw [hn,fieldSample]
    push_cast
    simpa only [sum_add_distrib,← mul_sum,mul_comm (v.jump _ : ℝ)] using H
  have hsum' : 10^9*(∑ j ∈ range 641, (v.jump j : ℝ)*logPrimitive ((((r : ℝ)+125*k)/40000-1)+1-125*j/40000)) =
      ∑ j ∈ range 641, (v.jump j : ℝ)*(10^9*logPrimitive (((r : ℝ)+125*k-125*j)/40000)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [show (((r : ℝ)+125*k)/40000-1)+1-125*j/40000=((r : ℝ)+125*k-125*j)/40000 by ring]
    ring
  rw [← hsum'] at hsum
  unfold realField sample
  push_cast
  linarith only [hsum]

end PiPolynomialValues
