module

public import OddPiPowers.PolynomialValues.Analysis.DerivativeProductBound
public import OddPiPowers.PolynomialValues.FourPeriod.IntegerDerivativeBlock

/-! A frequency Vandermonde with arbitrary column derivatives, including
coincident frequencies. The polynomial loss per derivative is explicit. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open MvPolynomial Finset

noncomputable def pairEnvelope {n : ℕ} (x : Fin n → ℤ) : ℝ :=
  ∏ e ∈ frequencyPairs n, (‖((x e.2-x e.1 : ℤ) : ℂ)‖+2)

def blockGrowth (n : ℕ) : ℕ := (frequencyPairs n).card+1

theorem pairEnvelope_nonneg {n : ℕ} (x : Fin n → ℤ) : 0 ≤ pairEnvelope x :=
  prod_nonneg (fun _ _ => by positivity)

private theorem linear_factor_majorant {n : ℕ} (x : Fin n → ℤ) (e : Fin n × Fin n) :
    PartialMajorant coordinateDerivative ((Int.castRingHom ℂ).comp (eval x))
      (‖((x e.2-x e.1 : ℤ) : ℂ)‖+2) 1 ((X e.2-X e.1 : MvPolynomial (Fin n) ℤ)) := by
  intro ds
  let φ := (Int.castRingHom ℂ).comp (eval x)
  let F : MvPolynomial (Fin n) ℤ := X e.2-X e.1
  let z (k : Fin n) : ℤ := (if e.2=k then 1 else 0)-(if e.1=k then 1 else 0)
  have hd (k : Fin n) : coordinateDerivative k F = C (z k) := by
    change pderiv k (X e.2-X e.1 : MvPolynomial (Fin n) ℤ) = _
    rw [map_sub]
    by_cases h₂ : e.2=k <;> by_cases h₁ : e.1=k <;> simp [z,h₂,h₁]
  cases ds with
  | nil =>
    change ‖φ F‖ ≤ _
    simpa [φ,F] using (show ‖((x e.2-x e.1 : ℤ) : ℂ)‖ ≤ ‖((x e.2-x e.1 : ℤ) : ℂ)‖+2 by linarith)
  | cons i ds =>
    change ‖φ (iterPartials coordinateDerivative ds (coordinateDerivative i F))‖ ≤ _
    rw [hd]
    cases ds with
    | nil =>
      change ‖φ (C (z i))‖ ≤ _
      have ha : ‖((z i : ℤ) : ℂ)‖ ≤ 2 := by
        by_cases h₂ : e.2=i <;> by_cases h₁ : e.1=i <;> norm_num [z,h₂,h₁]
      simpa only [φ,RingHom.comp_apply,eval_C,Int.coe_castRingHom,one_pow,mul_one] using
        ha.trans (le_add_of_nonneg_left (norm_nonneg _))
    | cons k ks =>
      have he : coordinateDerivative k (C (z i)) = 0 := pderiv_C
      change ‖φ (iterPartials coordinateDerivative ks (coordinateDerivative k (C (z i))))‖ ≤ _
      rw [he,map_zero,map_zero,norm_zero]
      positivity

theorem vandermonde_partial_norm {n : ℕ} (x : Fin n → ℤ) (ds : List (Fin n)) :
    ‖((eval x (iterPartials coordinateDerivative ds
      (Matrix.vandermonde (fun i : Fin n => (X i : MvPolynomial (Fin n) ℤ))).det) : ℤ) : ℂ)‖ ≤
    pairEnvelope x*(blockGrowth n : ℝ)^ds.length := by
  let F (e : Fin n × Fin n) : MvPolynomial (Fin n) ℤ := X e.2-X e.1
  let φ := (Int.castRingHom ℂ).comp (eval x)
  have he : (∏ e ∈ frequencyPairs n, F e) =
      (Matrix.vandermonde (fun i : Fin n => (X i : MvPolynomial (Fin n) ℤ))).det := by
    rw [Matrix.det_vandermonde]
    exact prod_finset_product (frequencyPairs n) univ (fun i => Ioi i) (fun e => by simp [frequencyPairs])
  have hh := partialMajorant_prod coordinateDerivative φ (fun _ => pderiv_one)
    (fun i f g => show pderiv i (f*g) = pderiv i f*g+f*pderiv i g from pderiv_mul)
    (frequencyPairs n) (fun e => ‖((x e.2-x e.1 : ℤ) : ℂ)‖+2) (fun _ => (1 : ℝ)) F
    (fun _ _ => by positivity) (fun _ _ => zero_le_one) (fun e _ => linear_factor_majorant x e) ds
  rw [he] at hh
  simp only [sum_const,nsmul_eq_mul,mul_one] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (pairEnvelope_nonneg x)
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact_mod_cast Nat.le_succ _

theorem exists_derivative_orders {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℕ) :
    ∃ ds : List ι, ds.length = ∑ j, r j ∧ ∀ j, ds.count j = r j := by
  have h (S : Finset ι) : ∃ ds : List ι, ds.length = ∑ j ∈ S, r j ∧ ∀ j, ds.count j = if j ∈ S then r j else 0 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨[],by simp,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨ds,hl,hc⟩ := ih
      refine ⟨List.replicate (r i) i++ds,by simp [hl,hi],?_⟩
      intro j
      by_cases he : j=i
      · subst j; simp [hc,hi]
      · simp [List.count_replicate,hc,he,Ne.symm he]
  simpa only [mem_univ,ite_true] using h univ

theorem integer_derivative_block_norm {n : ℕ} (x : Fin n → ℤ) (r : Fin n → ℕ) :
    ‖(((Matrix.of (fun i j : Fin n =>
        ((Polynomial.derivative^[r j]) ((Polynomial.X : Polynomial ℤ)^i.val)).eval (x j))).det : ℤ) : ℂ)‖ ≤
      pairEnvelope x*(blockGrowth n : ℝ)^(∑ j, r j) := by
  obtain ⟨ds,hl,hc⟩ := exists_derivative_orders r
  let P (_i j : Fin n) : Polynomial ℤ := Polynomial.X^j.val
  let A := Matrix.vandermonde (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))
  have hbase : columnMatrix (fun i j => P j i) = A.transpose := by
    ext i j
    simp [columnMatrix,inCoordinate,P,A,Matrix.vandermonde_apply]
  have he : MvPolynomial.eval x (iterPartials coordinateDerivative ds A.det) =
      (Matrix.of (fun i j : Fin n => ((Polynomial.derivative^[r j]) ((Polynomial.X : Polynomial ℤ)^i.val)).eval (x j))).det := by
    rw [← Matrix.det_transpose A,← hbase,iter_columnMatrix_det,RingHom.map_det]
    apply congrArg Matrix.det
    ext i j
    change (MvPolynomial.eval x) (inCoordinate j ((Polynomial.derivative^[ds.count j]) (P j i))) = _
    rw [hc]
    exact eval_inCoordinate x j ((Polynomial.derivative^[r j]) (P j i))
  rw [← he,← hl]
  exact vandermonde_partial_norm x ds

end PiPolynomialValues.FourPeriod
