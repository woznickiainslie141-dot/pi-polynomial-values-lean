module

public import OddPiPowers.PolynomialValues.FourPeriod.DifferentiatedProduct
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Data.Int.ModEq

/-! Prime-power divisibility of the differentiated frequency Vandermonde for
every list of coordinate derivatives and every integer frequency vector. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset MvPolynomial

def frequencyPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (univ ×ˢ univ).filter (fun e => e.1 < e.2)

def collidingPairs {n : ℕ} (p : ℤ) (x : Fin n → ℤ) : ℕ :=
  ((frequencyPairs n).filter fun e => x e.1 ≡ x e.2 [ZMOD p]).card

noncomputable def coordinateDerivative {n : ℕ} (i : Fin n) :
    MvPolynomial (Fin n) ℤ →+ MvPolynomial (Fin n) ℤ := (pderiv i).toLinearMap.toAddMonoidHom

theorem prime_power_dvd_vandermonde_derivative {n : ℕ} (p : ℤ) (x : Fin n → ℤ)
    (ds : List (Fin n)) :
    p ^ (collidingPairs p x - ds.length) ∣
      eval x (iterPartials coordinateDerivative ds
        (Matrix.vandermonde (fun i : Fin n => (X i : MvPolynomial (Fin n) ℤ))).det) := by
  let F (e : Fin n × Fin n) : MvPolynomial (Fin n) ℤ := X e.2 - X e.1
  have hprod : (∏ e ∈ frequencyPairs n, F e) =
      (Matrix.vandermonde (fun i : Fin n => (X i : MvPolynomial (Fin n) ℤ))).det := by
    rw [Matrix.det_vandermonde]
    exact Finset.prod_finset_product (frequencyPairs n) univ (fun i => Ioi i)
      (fun e => by simp [frequencyPairs])
  have hp := differentiated_product_dvd coordinateDerivative
    (fun i f g => show pderiv i (f*g) = pderiv i f*g + f*pderiv i g from pderiv_mul)
    (eval x) p (frequencyPairs n) F
    (fun e => x e.1 ≡ x e.2 [ZMOD p])
    (fun e _ he => by simpa only [F, map_sub, eval_X] using Int.modEq_iff_dvd.mp he) ds
  simpa only [collidingPairs, hprod] using hp

end PiPolynomialValues.FourPeriod
