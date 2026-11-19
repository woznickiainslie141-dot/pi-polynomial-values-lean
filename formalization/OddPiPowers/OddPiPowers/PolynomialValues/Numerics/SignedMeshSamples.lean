module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.All
public import OddPiPowers.PolynomialValues.Analysis.PrimitiveChord

/-! Integer samples at signed mesh differences. The odd extension of the
first primitive incurs at most two units of absolute error on either side. -/

@[expose] public section

namespace PiPolynomialValues

open Real Finset Certificates

def signedMeshF : ℤ → ℤ
  | .ofNat k => primitiveMesh.lookupF k
  | .negSucc k => -(primitiveMesh.lookupF (k+1))

theorem signedMeshF_error (k : ℤ) (hk : k.natAbs≤80000) :
    |10^9*logPrimitive ((k : ℝ)/40000)-(signedMeshF k : ℝ)| ≤ 2 := by
  have H := primitiveMesh_enclosed k.natAbs hk
  obtain ⟨h₁,h₂,_,_⟩ := H
  cases k with
  | ofNat k =>
    change |10^9*logPrimitive ((k : ℝ)/40000)-(primitiveMesh.lookupF k : ℝ)|≤2
    change (primitiveMesh.lookupF k : ℝ)≤10^9*logPrimitive ((k : ℝ)/40000) at h₁
    change 10^9*logPrimitive ((k : ℝ)/40000)≤(primitiveMesh.lookupF k : ℝ)+2 at h₂
    rw [abs_le]
    constructor <;> linarith
  | negSucc k =>
    change (primitiveMesh.lookupF (k+1) : ℝ)≤10^9*logPrimitive (((k+1 : ℕ) : ℝ)/40000) at h₁
    change 10^9*logPrimitive (((k+1 : ℕ) : ℝ)/40000)≤(primitiveMesh.lookupF (k+1) : ℝ)+2 at h₂
    rw [show Int.negSucc k = -((k+1 : ℕ) : ℤ) by rfl,Int.cast_neg,Int.cast_natCast,neg_div,logPrimitive_neg]
    change |10^9*(-logPrimitive (((k+1 : ℕ) : ℝ)/40000))-((-primitiveMesh.lookupF (k+1) : ℤ) : ℝ)|≤2
    rw [Int.cast_neg,abs_le]
    constructor <;> linarith

theorem meshF_word_range (k : ℕ) (hk : k≤80000) : |primitiveMesh.lookupF k| ≤ 2^31 := by
  let x := (k : ℝ)/40000
  have hx : 0≤x := by dsimp [x]; positivity
  have hx2 : x≤2 := by dsimp [x]; exact_mod_cast (show (k : ℝ)/40000≤2 by
    have : (k : ℝ)≤80000 := by exact_mod_cast hk
    linarith)
  have hlog : -2 ≤ logPrimitive x ∧ logPrimitive x ≤ 2 := by
    by_cases hz : x=0
    · norm_num [hz,logPrimitive]
    have h₁ := Real.self_sub_one_le_mul_log hx
    have h₂ := mul_le_mul_of_nonneg_left (Real.log_le_log (lt_of_le_of_ne hx (Ne.symm hz)) hx2) hx
    have l₂ := Real.log_le_sub_one_of_pos (by norm_num : 0<(2 : ℝ))
    have h₃ := mul_le_mul_of_nonneg_right (Real.log_nonneg (by norm_num : (1 : ℝ)≤2)) hx
    have h₄ := mul_le_mul_of_nonneg_right l₂ hx
    unfold logPrimitive
    constructor <;> nlinarith only [h₁,h₂,h₃,h₄,hx2]
  obtain ⟨h₁,h₂,_,_⟩ := primitiveMesh_enclosed k hk
  change (primitiveMesh.lookupF k : ℝ)≤10^9*logPrimitive x at h₁
  change 10^9*logPrimitive x≤(primitiveMesh.lookupF k : ℝ)+2 at h₂
  have hw : |(primitiveMesh.lookupF k : ℝ)| ≤ (2 : ℝ)^31 := by
    rw [abs_le]
    constructor <;> linarith only [h₁,h₂,hlog.1,hlog.2]
  exact_mod_cast hw

theorem signedMeshF_range (k : ℤ) (hk : k.natAbs≤80000) : |signedMeshF k|≤2^31 := by
  cases k with
  | ofNat k => exact meshF_word_range k hk
  | negSucc k => simpa only [signedMeshF,abs_neg] using meshF_word_range (k+1) hk

theorem mesh_field_sample_upper {ι : Type*} [Fintype ι] (i : ℤ) (e : ι → ℤ)
    (d : ι → ℤ) (h : ∀ j, (i-e j).natAbs≤80000) :
    (∑ j, (d j : ℝ)*(10^9*logPrimitive (((i-e j : ℤ) : ℝ)/40000))) ≤
      ((∑ j : ι, (d j*signedMeshF (i-e j)+2*|d j|) : ℤ) : ℝ) := by
  push_cast
  apply sum_le_sum
  intro j _
  have H := signedMeshF_error (i-e j) (h j)
  have ha := (le_abs_self ((d j : ℝ)*(10^9*logPrimitive (((i-e j : ℤ) : ℝ)/40000)-
    (signedMeshF (i-e j) : ℝ)))).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left H (abs_nonneg _)))
  push_cast at ha ⊢
  linarith only [ha]

end PiPolynomialValues
