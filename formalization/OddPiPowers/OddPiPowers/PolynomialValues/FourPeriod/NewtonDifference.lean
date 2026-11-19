module

public import OddPiPowers.PolynomialValues.FourPeriod.NewtonRows
public import Mathlib.Algebra.Group.ForwardDiff

/-! Exact integral finite differences on the monic Newton basis and the
commutation of these differences with coefficient maps and derivatives. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

noncomputable def polynomialDifference {R : Type*} [CommRing R] (step : R) (f : R[X]) : R[X] :=
  f.comp (X+C step) - f

theorem polynomialDifference_C_mul {R : Type*} [CommRing R] (step b : R) (f : R[X]) :
    polynomialDifference step (C b*f) = C b * polynomialDifference step f := by
  simp only [polynomialDifference,mul_comp,C_comp,mul_sub]

theorem polynomialDifference_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (step : R) (f : R[X]) : (polynomialDifference step f).map φ =
      polynomialDifference (φ step) (f.map φ) := by
  simp only [polynomialDifference,Polynomial.map_sub,map_comp,Polynomial.map_add,map_X,map_C]

theorem iterate_difference_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (step : R) (f : R[X]) (k : ℕ) : (((polynomialDifference step)^[k]) f).map φ =
      ((polynomialDifference (φ step))^[k]) (f.map φ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply',polynomialDifference_map,ih]

theorem newton_difference_iter (step m k : ℕ) (a : ℤ) :
    ((polynomialDifference (step : ℤ))^[k]) (newtonRow step a m) =
      C ((m.descFactorial k : ℤ)*(step : ℤ)^k) * newtonRow step a (m-k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,polynomialDifference_C_mul]
    cases he : m-k with
    | zero =>
      have hh : m < k+1 := by omega
      rw [Nat.descFactorial_of_lt hh]
      simp [newtonRow,polynomialDifference]
    | succ r =>
      have hh : m-(k+1) = r := by omega
      rw [polynomialDifference,newtonRow_comp_shift,newtonRow_step,Nat.descFactorial_succ,he,hh,pow_succ]
      simp only [Nat.cast_mul,Nat.cast_succ,map_mul,map_add,map_one]
      ring

theorem polynomialDifference_derivative {R : Type*} [CommRing R] (step : R) (f : R[X]) :
    (polynomialDifference step f).derivative = polynomialDifference step f.derivative := by
  simp only [polynomialDifference,derivative_sub,derivative_comp,derivative_add,derivative_X,derivative_C,
    add_zero,one_mul]

theorem eval_polynomialDifference_iter {R : Type*} [CommRing R] (step : R) (f : R[X]) (k : ℕ) (x : R) :
    (((polynomialDifference step)^[k]) f).eval x = ((fwdDiff step)^[k]) (fun z => f.eval z) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',polynomialDifference, eval_sub,eval_comp]
    simp only [eval_add,eval_X,eval_C,ih,fwdDiff]

end PiPolynomialValues.FourPeriod
