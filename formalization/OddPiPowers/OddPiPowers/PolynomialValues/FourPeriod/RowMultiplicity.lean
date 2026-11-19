module

public import OddPiPowers.PolynomialValues.FourPeriod.Degree
public import OddPiPowers.PolynomialValues.FourPeriod.Symbol

/-! For an arbitrary integral row polynomial, each imposed frequency root
consumes one derivative before a coefficient in the argument can survive. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial OddPiPowers

theorem rowOperator_add {A : Type*} [CommRing A] (s u : A) (j : ℕ) (p q : A[X]) :
    rowOperator s u j (p+q) = rowOperator s u j p + rowOperator s u j q := by
  induction j with
  | zero => rfl
  | succ j ih => rw [rowOperator, ih, rowStep_add]; rfl

noncomputable def entryWithRow (v t : ℤ) (j : ℕ) : GaussianInt[X] →+ GaussianInt[X] where
  toFun p := C (phase (v*t)) *
    (rowOperator (2 : GaussianInt[X]) (nodeCoefficient v) j
      (p.map (C : GaussianInt →+* GaussianInt[X]))).eval (C (t : GaussianInt))
  map_zero' := by rw [Polynomial.map_zero, rowOperator_zero, eval_zero, mul_zero]
  map_add' p q := by rw [Polynomial.map_add, rowOperator_add, eval_add, mul_add]

theorem entryWithRow_monomial (v t : ℤ) (j σ : ℕ) :
    entryWithRow v t j (X^σ) = rawEntry v t σ j := by
  simp only [entryWithRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Polynomial.map_pow,
    Polynomial.map_X, rawEntry]

theorem entryWithRow_C_mul (v t : ℤ) (j : ℕ) (c : GaussianInt) (p : GaussianInt[X]) :
    entryWithRow v t j (C c * p) = C c * entryWithRow v t j p := by
  simp only [entryWithRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Polynomial.map_mul, map_C,
    rowOperator_C_mul, eval_mul, eval_C]
  ring

theorem entryWithRow_succ (v t : ℤ) (j : ℕ) (p : GaussianInt[X]) :
    entryWithRow v t (j+1) p =
      2 * entryWithRow v t j p.derivative + nodeCoefficient v * entryWithRow v t j p := by
  simp only [entryWithRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, rowOperator, rowStep,
    eval_add, eval_mul, eval_C, derivative_rowOperator, derivative_map]
  ring

theorem entryWithRow_expansion (v t : ℤ) (j : ℕ) (p : GaussianInt[X]) (m : ℕ)
    (hm : p.natDegree < m) :
    entryWithRow v t j p = ∑ r ∈ Finset.range m, C (p.coeff r) * rawEntry v t r j := by
  calc
    _ = entryWithRow v t j (∑ r ∈ Finset.range m, C (p.coeff r) * X^r) :=
      congrArg (entryWithRow v t j) (p.as_sum_range_C_mul_X_pow' hm)
    _ = _ := by simp only [map_sum, entryWithRow_C_mul, entryWithRow_monomial]

theorem entryWithRow_coeff_vanish (v t : ℤ) (j r k : ℕ) (p : GaussianInt[X])
    (hp : (X-C (t : GaussianInt))^r ∣ p) (hk : j < k+r) :
    (entryWithRow v t j p).coeff k = 0 := by
  induction j generalizing r k p with
  | zero =>
    have he : entryWithRow v t 0 p = C (phase (v*t) * p.eval (t : GaussianInt)) := by
      simp only [entryWithRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, rowOperator, eval_map_apply, map_mul]
    rw [he]
    by_cases hz : k = 0
    · subst k
      have hlin : X-C (t : GaussianInt) ∣ p := (dvd_pow_self _ (by omega : r ≠ 0)).trans hp
      obtain ⟨q,hq⟩ := hlin
      have hr : p.eval (t : GaussianInt) = 0 := by simp [hq]
      simp [hr]
    · simp [coeff_C, hz]
  | succ j ih =>
    have hder := ih (r-1) k p.derivative (pow_sub_one_dvd_derivative_of_pow_dvd hp) (by omega)
    have htwo : (2 : GaussianInt[X]) = C (2 : GaussianInt) := (map_ofNat C 2).symm
    rw [entryWithRow_succ, htwo, nodeCoefficient, mul_assoc, coeff_add, coeff_C_mul, hder,
      mul_zero, zero_add, coeff_C_mul]
    cases k with
    | zero => simp only [coeff_X_mul_zero, mul_zero]
    | succ k => rw [coeff_X_mul, ih r k p hp (by omega), mul_zero]

theorem entryWithRow_degree_loss (v t : ℤ) (j r : ℕ) (p : GaussianInt[X])
    (hp : (X-C (t : GaussianInt))^r ∣ p) (hn : entryWithRow v t j p ≠ 0) :
    (entryWithRow v t j p).natDegree + r ≤ j := by
  by_contra! ht
  have hc := entryWithRow_coeff_vanish v t j r _ p hp ht
  rw [coeff_natDegree] at hc
  exact (leadingCoeff_ne_zero.mpr hn) hc

end PiPolynomialValues.FourPeriod
