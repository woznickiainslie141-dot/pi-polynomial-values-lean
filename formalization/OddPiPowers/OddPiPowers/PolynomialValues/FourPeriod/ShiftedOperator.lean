module

public import OddPiPowers.PolynomialValues.FourPeriod.RowOperator
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Algebra.Basic

/-! Exact binomial perturbation of a column operator, retaining its
derivative order and its independent perturbation label. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

variable {A : Type*} [CommRing A]

noncomputable def shiftedEnd (z : A) : Module.End A A[X] :=
  Polynomial.derivative + algebraMap A (Module.End A A[X]) z

theorem shiftedEnd_pow (z : A) (j : ℕ) (P : A[X]) : (shiftedEnd z^j) P = rowOperator 1 z j P := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',Module.End.mul_apply,ih]
    simp only [shiftedEnd,LinearMap.add_apply,Module.algebraMap_end_apply,Polynomial.smul_eq_C_mul,
      rowOperator,rowStep,map_one,one_mul]

theorem rowOperator_perturb (z δ : A) (j : ℕ) (P : A[X]) :
    rowOperator 1 (z+δ) j P =
      ∑ l ∈ range (j+1), C ((j.choose l : A)*δ^l)*rowOperator 1 z (j-l) P := by
  let φ := algebraMap A (Module.End A A[X])
  have he : shiftedEnd (z+δ) = φ δ+shiftedEnd z := by
    unfold shiftedEnd φ
    rw [map_add]
    ac_rfl
  have h := (Algebra.commute_algebraMap_left δ (shiftedEnd z)).add_pow j
  rw [← shiftedEnd_pow,he,show (φ δ+shiftedEnd z)^j = _ from h,LinearMap.sum_apply]
  apply sum_congr rfl
  intro l _
  rw [← map_pow φ,Module.End.mul_apply,Module.End.mul_apply,Module.End.natCast_apply,map_nsmul,
    shiftedEnd_pow]
  change (δ^l) • (j.choose l • rowOperator 1 z (j-l) P) = _
  rw [Polynomial.smul_eq_C_mul,nsmul_eq_mul,map_mul]
  simp only [← C_eq_natCast]
  ring

theorem rowOperator_expansion (z : A) (j : ℕ) (P : A[X]) :
    rowOperator 1 z j P = ∑ l ∈ range (j+1), C ((j.choose l : A)*z^l)*(derivative^[j-l]) P := by
  have hz (k : ℕ) : rowOperator 1 (0 : A) k P = (derivative^[k]) P := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [rowOperator,rowStep,map_zero,map_one,one_mul,zero_mul,add_zero,ih,
        Function.iterate_succ_apply']
  simpa only [zero_add,hz] using rowOperator_perturb (0 : A) z j P

end PiPolynomialValues.FourPeriod
