module

public import OddPiPowers.PolynomialValues.FourPeriod.RowSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Analytic.Order

/-! The normalized row at a complex path value is the divided Taylor
derivative of the single column function z^j exp(t z). -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

theorem iteratedDeriv_id_product {f : ℂ → ℂ} (hf : ContDiff ℂ ⊤ f) (m : ℕ) :
    iteratedDeriv (m+1) (fun z => z*f z) =
      fun z => z*iteratedDeriv (m+1) f z+((m : ℂ)+1)*iteratedDeriv m f z := by
  have hd (n : ℕ) (z : ℂ) : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f z) z := by
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv n (by simp) z).hasDerivAt
  induction m with
  | zero =>
    funext z
    rw [iteratedDeriv_succ,iteratedDeriv_zero]
    have h := (hasDerivAt_id z).mul (by simpa only [iteratedDeriv_zero] using hd 0 z)
    rw [show (fun s : ℂ => s*f s) = id*f from funext (fun _ => rfl)]
    simpa [id_eq,Pi.mul_apply,add_comm] using h.deriv
  | succ m ih =>
    rw [iteratedDeriv_succ (n := m+1),ih]
    funext z
    have h := ((hasDerivAt_id z).mul (hd (m+1) z)).add ((hd m z).const_mul ((m : ℂ)+1))
    have he : deriv (fun z => z*iteratedDeriv (m+1) f z+((m : ℂ)+1)*iteratedDeriv m f z) z =
        1*iteratedDeriv (m+1) f z+z*iteratedDeriv (m+1+1) f z+((m : ℂ)+1)*iteratedDeriv (m+1) f z := h.deriv
    rw [he,Nat.cast_succ]
    ring

noncomputable def columnFunction (t : ℂ) (j : ℕ) (z : ℂ) := z^j*Complex.exp (t*z)

theorem columnFunction_contDiff (t : ℂ) (j : ℕ) : ContDiff ℂ ⊤ (columnFunction t j) := by
  unfold columnFunction
  fun_prop

noncomputable def dividedRow (σ : ℕ) (f : ℂ → ℂ) (z : ℂ) := (σ.factorial : ℂ)⁻¹*iteratedDeriv σ f z

theorem dividedRow_columnFunction (t : ℂ) (j σ : ℕ) (z : ℂ) :
    dividedRow σ (columnFunction t j) z =
      Complex.exp (t*z)*(rowOperator 1 z j (normalizedRowPolynomial σ)).eval t := by
  induction j generalizing σ with
  | zero =>
    rw [dividedRow,show columnFunction t 0 = fun z => Complex.exp (t*z) by funext z; simp [columnFunction],
      iteratedDeriv_cexp_const_mul]
    simp only [rowOperator,
      normalizedRowPolynomial,eval_mul,eval_C,eval_pow,eval_X]
    ring
  | succ j ih =>
    have he : columnFunction t (j+1) = fun u => u*columnFunction t j u := by
      funext u
      simp only [columnFunction,pow_succ']
      ring
    rw [he]
    cases σ with
    | zero =>
      have hz := ih 0
      simp only [dividedRow,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,inv_one,one_mul] at hz ⊢
      rw [hz,rowOperator,rowStep,eval_add,eval_mul,eval_mul,eval_C,eval_C,one_mul,
        derivative_rowOperator]
      simp [normalizedRowPolynomial,rowOperator_zero]
      ring
    | succ k =>
      have h1 := ih (k+1)
      have h0 := ih k
      have hc : ((k+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have step : dividedRow (k+1) (fun u => u*columnFunction t j u) z =
          z*dividedRow (k+1) (columnFunction t j) z+dividedRow k (columnFunction t j) z := by
        rw [dividedRow,iteratedDeriv_id_product (columnFunction_contDiff t j)]
        simp only [dividedRow,Nat.factorial_succ,Nat.cast_mul]
        push_cast at hc ⊢
        field_simp
        <;> ring
      rw [step,h1,h0,rowOperator,rowStep,eval_add,eval_mul,eval_mul,eval_C,eval_C,
        one_mul,derivative_rowOperator,derivative_normalizedRowPolynomial]
      ring

end PiPolynomialValues.FourPeriod
