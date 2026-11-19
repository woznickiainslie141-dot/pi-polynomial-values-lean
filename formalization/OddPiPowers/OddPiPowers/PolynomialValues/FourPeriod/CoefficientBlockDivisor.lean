module

public import OddPiPowers.PolynomialValues.FourPeriod.EntryCoefficients
public import OddPiPowers.PolynomialValues.FourPeriod.IntegerDerivativeBlock
public import OddPiPowers.PolynomialValues.FourPeriod.NodeBlockExpansion
public import OddPiPowers.PolynomialValues.FourPeriod.ColumnCoefficientExpansion

/-! Every square node block of a homogeneous coefficient is a Gaussian
column factor times an actual integer differentiated Vandermonde. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset OddPiPowers

private theorem list_with_counts {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℕ) :
    ∃ ds : List ι, ds.length = ∑ i ∈ S, f i ∧ ∀ i, ds.count i = if i ∈ S then f i else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨[],by simp,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨ds,hl,hc⟩ := ih
    refine ⟨List.replicate (f a) a ++ ds,by simp [hl,ha],?_⟩
    intro i
    by_cases he : i=a
    · subst i
      simp [hc,ha]
    · simp [List.count_replicate,hc,he,Ne.symm he]

private theorem int_cast_monomial_derivative (σ k : ℕ) (t : ℤ) :
    ((derivative^[k]) ((X : GaussianInt[X])^σ)).eval (t : GaussianInt) =
      (Int.castRingHom GaussianInt) (((derivative^[k]) ((X : ℤ[X])^σ)).eval t) := by
  let φ := Int.castRingHom GaussianInt
  have he : ((X : ℤ[X])^σ).map φ = X^σ := by rw [Polynomial.map_pow,map_X]
  rw [← he,iterate_derivative_map]
  exact eval_map_apply φ t

theorem coeff_node_block_dvd {n : ℕ} (p : ℕ) (v : ℤ) (x : Fin n → ℤ) (j h : Fin n → ℕ) :
    (p : GaussianInt)^(collidingPairs p x - ∑ i, (j i-h i)) ∣
      (Matrix.of (fun r c : Fin n => (rawEntry v (x c) r.val (j c)).coeff (h c))).det := by
  let D (c : Fin n) := j c-h c
  obtain ⟨ds,hl,hc⟩ := list_with_counts (univ : Finset (Fin n)) D
  have he (c : Fin n) : ds.count c = D c := by simpa using hc c
  let M : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun r c =>
    ((derivative^[D c]) ((X : ℤ[X])^r.val)).eval (x c)
  have hd : (p : ℤ)^(collidingPairs p x - ∑ i, D i) ∣ M.det := by
    have hraw := integer_derivative_block_divisible (p : ℤ) x ds
    simpa only [hl,he,M] using hraw
  let φ := Int.castRingHom GaussianInt
  have hm : (p : GaussianInt)^(collidingPairs p x - ∑ i, D i) ∣ (M.map φ).det := by
    change _ ∣ (φ.mapMatrix M).det
    rw [← φ.map_det M]
    simpa only [map_pow,map_natCast] using map_dvd φ hd
  let b (c : Fin n) := (derivativeWeight (j c) (h c) : GaussianInt) * phase (v*x c) *
    ((v : GaussianInt)*gaussianI)^(h c)
  have hmat : (Matrix.of (fun r c : Fin n => (rawEntry v (x c) r.val (j c)).coeff (h c))) =
      Matrix.of (fun r c => b c*(M.map φ) r c) := by
    apply Matrix.ext
    intro r c
    simp only [Matrix.of_apply,← entryWithRow_monomial,entryWithRow_coefficient,int_cast_monomial_derivative,
      b,M,Matrix.map_apply,D,φ]
  rw [hmat,Matrix.det_mul_row]
  exact dvd_mul_of_dvd_right hm _

end PiPolynomialValues.FourPeriod
