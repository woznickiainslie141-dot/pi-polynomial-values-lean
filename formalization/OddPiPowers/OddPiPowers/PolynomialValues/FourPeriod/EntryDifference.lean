module

public import OddPiPowers.PolynomialValues.FourPeriod.NewtonDifference
public import OddPiPowers.PolynomialValues.FourPeriod.NewtonDeterminant

/-! Consecutive columns in the same layer and residue have constant
fourth-root phase. Their differences act directly on the integer Newton row. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

private theorem phase_step_four (v t : ℤ) : phase (v*(t+4)) = phase (v*t) := by
  unfold phase
  rw [mul_add,Int.add_mul_emod_self_right]

theorem entryWithRow_shift_four (v t : ℤ) (j : ℕ) (p : GaussianInt[X]) :
    entryWithRow v (t+4) j p = entryWithRow v t j (p.comp (X+C 4)) := by
  induction j generalizing p with
  | zero =>
    simp only [entryWithRow,AddMonoidHom.coe_mk,ZeroHom.coe_mk,rowOperator,eval_map_apply,
      eval_comp,eval_add,eval_X,eval_C,Int.cast_add,Int.cast_ofNat,phase_step_four]
  | succ j ih =>
    rw [entryWithRow_succ,entryWithRow_succ,ih p,ih p.derivative,derivative_comp]
    simp only [derivative_add,derivative_X,derivative_C,add_zero,one_mul]

theorem entryWithRow_difference_four (v t : ℤ) (j : ℕ) (p : GaussianInt[X]) :
    fwdDiff (4 : ℤ) (fun u => entryWithRow v u j p) t =
      entryWithRow v t j (polynomialDifference 4 p) := by
  rw [polynomialDifference,map_sub,← entryWithRow_shift_four]
  rfl

theorem entryWithRow_difference_iter (v t : ℤ) (j k : ℕ) (p : GaussianInt[X]) :
    ((fwdDiff (4 : ℤ))^[k]) (fun u => entryWithRow v u j p) t =
      entryWithRow v t j (((polynomialDifference 4)^[k]) p) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change _ - _ = _
    rw [ih,ih]
    exact entryWithRow_difference_four _ _ _ _

theorem differenced_newton_entry (v t a : ℤ) (j σ k : ℕ) :
    ((fwdDiff (4 : ℤ))^[k]) (fun u => entryWithRow v u j (gaussianNewton 4 a σ)) t =
      C (((σ.descFactorial k : ℕ) : GaussianInt)*4^k) *
        entryWithRow v t j (gaussianNewton 4 a (σ-k)) := by
  rw [entryWithRow_difference_iter]
  let φ := Int.castRingHom GaussianInt
  have he := iterate_difference_map φ (4 : ℤ) (newtonRow 4 a σ) k
  change _ = ((polynomialDifference (4 : GaussianInt))^[k]) (gaussianNewton 4 a σ) at he
  have hf := newton_difference_iter 4 σ k a
  change ((polynomialDifference (4 : ℤ))^[k]) (newtonRow 4 a σ) = _ at hf
  rw [← he,hf,Polynomial.map_mul,map_C,entryWithRow_C_mul]
  simp only [φ,map_mul,map_natCast,map_pow,map_ofNat,Nat.cast_ofNat,gaussianNewton]

theorem differenced_newton_entry_zero {v t a : ℤ} {j σ k : ℕ} (h : σ < k) :
    ((fwdDiff (4 : ℤ))^[k]) (fun u => entryWithRow v u j (gaussianNewton 4 a σ)) t = 0 := by
  rw [differenced_newton_entry,Nat.descFactorial_of_lt h]
  simp

end PiPolynomialValues.FourPeriod
