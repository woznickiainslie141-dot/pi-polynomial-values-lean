module

public import OddPiPowers.PolynomialValues.FixedFactor
public import OddPiPowers.PolynomialValues.DiskEvaluation
public import OddPiPowers.Transfer.AuxiliaryFamily
public import OddPiPowers.Transfer.ResultantBound
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Fixed-scale exclusion of Gaussian annihilators of degree at most three. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial OddPiPowers

private theorem cubic_rate_product_lt_one {C K D G n : ℝ}
    (hn : C * K ^ 2 < (D - 2 * G - 3) * n) :
    C * (Real.exp (-(D - 1) * n) * (K * Real.exp ((G + 1) * n)) ^ 2) < 1 := by
  have he : Real.exp (-(D - 1) * n) * (Real.exp ((G + 1) * n)) ^ 2 =
      (Real.exp ((D - 2 * G - 3) * n))⁻¹ := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  calc
    _ = (C * K ^ 2) / Real.exp ((D - 2 * G - 3) * n) := by
      rw [mul_pow, div_eq_mul_inv, ← he]
      ring
    _ < 1 := (div_lt_one (Real.exp_pos _)).mpr
      (hn.trans ((lt_add_one _).trans_le (Real.add_one_le_exp _)))

/-- An actual auxiliary family with excess decay at the center excludes every
fixed nonzero Gaussian polynomial of degree at most three at that center. -/
theorem cubic_nonvanishing_of_family {m L : ℕ} {D G : ℝ} (hL : 0 < L)
    (hG : 0 ≤ G) (hgap : 0 < D - 2 * G - 3)
    {U : ℕ → Fin (m + 1) → GaussianInt[X]} (hU : AuxiliaryFamily m L D G U)
    (F : GaussianInt[X]) (hF : F ≠ 0) (hd : F.natDegree ≤ 3) :
    F.eval₂ GaussianInt.toComplex lambda ≠ 0 := by
  classical
  intro hx
  obtain ⟨f, hf, hdeg, hfroot, hres⟩ := exists_gaussian_fixed_factor F lambda hF hx
  let S := (f.map GaussianInt.toComplex).roots.toFinset
  obtain ⟨K, hK, hKbound⟩ := exists_disk_evaluation_constant m S
  let B : NNReal := max 1 ‖(f.leadingCoeff : ℂ)‖₊
  let β := D - 2 * G - 3
  have hβ : 0 < β := hgap
  obtain ⟨N, hN⟩ := hU.bounds 1 zero_lt_one
  obtain ⟨r₀, hr₀⟩ := exists_nat_gt (((B : ℝ) ^ m * K ^ 2) / β)
  let r := max (N + 1) r₀
  have hr : 0 < r := (Nat.succ_pos N).trans_le (le_max_left _ _)
  have hrn : r ≤ L * r := Nat.le_mul_of_pos_left _ hL
  have hnr : N ≤ L * r := (Nat.le_succ N).trans ((le_max_left _ _).trans hrn)
  let n := ((L * r : ℕ) : ℝ)
  have hlarge : (B : ℝ) ^ m * K ^ 2 < β * n := by
    have hr₁ : (r₀ : ℝ) ≤ n := Nat.cast_le.mpr ((le_max_right (N + 1) r₀).trans hrn)
    simpa only [mul_comm β n] using (div_lt_iff₀ hβ).mp (hr₀.trans_le hr₁)
  obtain ⟨hsmall, hdisk, _⟩ := hN r hr hnr
  obtain ⟨i, hi⟩ := exists_polynomial_nonzero_row m (U (L * r)) (hU.degree r hr)
    (hU.determinant r hr) lambda
  let R := U (L * r) i
  let H := Real.exp ((G + 1) * n)
  have hH : 1 ≤ H := Real.one_le_exp (by dsimp [n]; positivity)
  have hKH : 1 ≤ K * H := one_le_mul_of_one_le_of_one_le hK hH
  let T : NNReal := ⟨K * H, zero_le_one.trans hKH⟩
  have hT : 1 ≤ T := hKH
  have hRdeg : (R.map GaussianInt.toComplex).natDegree ≤ m := by
    rw [natDegree_map_eq_of_injective GaussianInt.toComplex_injective]
    exact hU.degree r hr i
  have hrootvalues (z : ℂ) (hz : z ∈ (f.map GaussianInt.toComplex).roots) :
      ‖(R.map GaussianInt.toComplex).eval z‖₊ ≤ T := by
    change ‖(R.map GaussianInt.toComplex).eval z‖ ≤ K * H
    exact hKbound _ H hRdeg (Real.exp_pos _).le (hdisk i) z (Multiset.mem_toFinset.mpr hz)
  have hprod := gaussian_resultant_product_bound f R lambda hf hfroot (hres R hi) m 3
    (hdeg.trans hd) (hU.degree r hr i) B T (le_max_left _ _) hT (le_max_right _ _)
    hrootvalues (IsAlgClosed.splits _)
  have hlo : 1 ≤ (B : ℝ) ^ m * (‖(complexPolynomial R).eval lambda‖ * (K * H) ^ 2) := by
    exact_mod_cast hprod
  have hup : (B : ℝ) ^ m * (‖(complexPolynomial R).eval lambda‖ * (K * H) ^ 2) ≤
      (B : ℝ) ^ m * (Real.exp (-(D - 1) * n) * (K * H) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg B.coe_nonneg _)
    exact mul_le_mul_of_nonneg_right (hsmall i) (sq_nonneg _)
  exact (not_lt_of_ge (hlo.trans hup)) (cubic_rate_product_lt_one hlarge)

end PiPolynomialValues
