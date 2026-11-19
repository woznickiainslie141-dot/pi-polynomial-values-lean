module

public import OddPiPowers.PolynomialValues.Analysis.VandermondeNorm
public import OddPiPowers.PolynomialValues.FourPeriod.ShiftedOperator
public import OddPiPowers.PolynomialValues.FourPeriod.Normalization

/-! The shifted complete-prefix block at every complex path value has
an explicit product bound, with repeated integer frequencies allowed. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

theorem det_sum_columns_norm {n : ℕ} {ι : Fin n → Type*} [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → ℂ) (v : ∀ j, ι j → Fin n → ℂ) (b : ∀ j, ι j → ℝ) (U : ℝ)
    (h : ∀ k : ∀ j, ι j, ‖(Matrix.of fun i j => v j (k j) i).det‖ ≤ U * ∏ j, b j (k j)) :
    ‖(Matrix.of (fun i j => ∑ k, c j k * v j k i)).det‖ ≤
      U * ∏ j, ∑ k, ‖c j k‖*b j k := by
  classical
  let L := (Matrix.detRowAlternating (n := Fin n) (R := ℂ)).toMultilinearMap
  let A := Matrix.of (fun i j => ∑ k, c j k * v j k i)
  have he : A.transpose.det = L (fun j => ∑ k, c j k • v j k) := by
    apply congrArg Matrix.det
    ext i j
    simp [A,Pi.smul_apply]
  change ‖A.det‖ ≤ _
  rw [← Matrix.det_transpose A,he,L.map_sum]
  apply (norm_sum_le _ _).trans
  rw [Fintype.prod_sum,mul_sum]
  apply sum_le_sum
  intro k _
  rw [L.map_smul_univ,smul_eq_mul,norm_mul,norm_prod,prod_mul_distrib]
  have hh : ‖L (fun j => v j (k j))‖ ≤ U*∏ j, b j (k j) := by
    change ‖(Matrix.of fun j i => v j (k j) i).det‖ ≤ _
    rw [← Matrix.det_transpose]
    exact h k
  calc
    _ ≤ (∏ j, ‖c j (k j)‖)*(U*∏ j, b j (k j)) := mul_le_mul_of_nonneg_left hh (prod_nonneg (fun j _ => norm_nonneg _))
    _ = _ := by ring

noncomputable def shiftedBlock {n : ℕ} (x : Fin n → ℤ) (j : Fin n → ℕ) (z : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i c =>
      (rowOperator 1 (z c) (j c) ((X : ℂ[X])^i.val)).eval (x c : ℂ)

theorem shiftedBlock_bound {n : ℕ} (x : Fin n → ℤ) (j : Fin n → ℕ) (z : Fin n → ℂ) :
    ‖(shiftedBlock x j z).det‖ ≤ pairEnvelope x*∏ c, (‖z c‖+blockGrowth n)^(j c) := by
  let B := (blockGrowth n : ℝ)
  let a (c : Fin n) (l : Fin (j c+1)) := ((j c).choose l.val : ℂ)*(z c)^l.val
  let v (c : Fin n) (l : Fin (j c+1)) (i : Fin n) :=
    ((derivative^[j c-l.val]) ((X : ℂ[X])^i.val)).eval (x c : ℂ)
  let w (c : Fin n) (l : Fin (j c+1)) := B^(j c-l.val)
  have he : shiftedBlock x j z = Matrix.of (fun i c => ∑ l, a c l * v c l i) := by
    ext i c
    change (rowOperator 1 (z c) (j c) ((X : ℂ[X])^i.val)).eval (x c : ℂ) = _
    rw [rowOperator_expansion,eval_finsetSum]
    simp only [Matrix.of_apply,eval_mul,eval_C]
    exact (Fin.sum_univ_eq_sum_range (fun l => ((j c).choose l : ℂ)*z c^l*
      ((derivative^[j c-l]) ((X : ℂ[X])^i.val)).eval (x c : ℂ)) (j c+1)).symm
  have hc (k : ∀ c, Fin (j c+1)) :
      ‖(Matrix.of fun i c => v c (k c) i).det‖ ≤ pairEnvelope x*∏ c, w c (k c) := by
    let d (c : Fin n) := j c-(k c).val
    let M := Matrix.of (fun i c : Fin n => ((derivative^[d c]) ((X : ℤ[X])^i.val)).eval (x c))
    let φ := Int.castRingHom ℂ
    have hm : φ.mapMatrix M = Matrix.of fun i c => v c (k c) i := by
      ext i c
      change φ ((((derivative^[d c]) ((X : ℤ[X])^i.val)).eval (x c))) = _
      have hd : ((X : ℤ[X])^i.val).map φ = X^i.val := by rw [Polynomial.map_pow,map_X]
      change _ = ((derivative^[d c]) ((X : ℂ[X])^i.val)).eval (φ (x c))
      rw [← hd,iterate_derivative_map,eval_map_apply]
    rw [← hm,← φ.map_det]
    change _ ≤ pairEnvelope x*∏ c, B^(d c)
    rw [prod_pow_eq_pow_sum]
    exact integer_derivative_block_norm x d
  have hs (c : Fin n) : (∑ l, ‖a c l‖*w c l) = (‖z c‖+B)^(j c) := by
    rw [add_pow]
    have h₁ := Fin.sum_univ_eq_sum_range (fun l => ‖((j c).choose l : ℂ)*z c^l‖*B^(j c-l)) (j c+1)
    rw [show (∑ l, ‖a c l‖*w c l) = _ from h₁]
    apply sum_congr rfl
    intro l _
    rw [norm_mul,Complex.norm_natCast,norm_pow]
    ring
  rw [he]
  exact (det_sum_columns_norm a v w (pairEnvelope x) hc).trans_eq (by simp only [hs,B])

end PiPolynomialValues.FourPeriod
