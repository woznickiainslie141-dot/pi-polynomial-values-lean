module

public import OddPiPowers.PolynomialValues.Endpoint
public import OddPiPowers.PolynomialValues.FixedRootCriterion
public import OddPiPowers.Transfer.TwelveLayerPiCube

/-! Exact nonvanishing of all integer polynomial values of degree at most three
at pi, using the proved decay and disk bounds of the actual twelve-layer rows. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial OddPiPowers

theorem complex_value_at_real (P : ℤ[X]) (x : ℝ) :
    P.eval₂ (Int.castRingHom ℂ) (x : ℂ) = (value x P : ℂ) := by
  have hcomp : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := Subsingleton.elim _ _
  have h := hom_eval₂ P (Int.castRingHom ℝ) Complex.ofRealHom x
  rw [hcomp] at h
  exact h.symm

/-- No nonzero integer polynomial of degree at most three has pi as a root. -/
theorem pi_cubic_value_ne_zero (P : ℤ[X]) (hP : P ≠ 0) (hd : P.natDegree ≤ 3) :
    value Real.pi P ≠ 0 := by
  intro hzero
  let a : GaussianInt := -2 * gaussianI
  have hI : gaussianI ≠ 0 := by decide
  have ha : a ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (by norm_num)) hI
  let T : GaussianInt[X] := C a * X
  have hT : T.natDegree = 1 := natDegree_C_mul_X a ha
  let ι := Int.castRingHom GaussianInt
  have hι : Function.Injective ι := Int.cast_injective
  let F := (P.map ι).comp T
  have hn : F ≠ 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with hz | ⟨_, hconst⟩
    · exact (Polynomial.map_ne_zero_iff hι).mpr hP hz
    · have he := congrArg natDegree hconst
      rw [hT, natDegree_C] at he
      contradiction
  have hdegree : F.natDegree ≤ 3 := by
    simpa only [F, natDegree_comp, hT, mul_one, natDegree_map_eq_of_injective hι] using hd
  have haC : GaussianInt.toComplex a = -2 * Complex.I := by
    simp only [a, map_mul, map_neg, map_ofNat]
    rw [show GaussianInt.toComplex gaussianI = Complex.I from gaussianI_toComplex]
  have hy : GaussianInt.toComplex a * lambda = (Real.pi : ℂ) := by
    rw [haC]
    calc
      _ = -(Complex.I * Complex.I) * (Real.pi : ℂ) := by unfold lambda; ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have hcomp : GaussianInt.toComplex.comp ι = Int.castRingHom ℂ := Subsingleton.elim _ _
  have hroot : F.eval₂ GaussianInt.toComplex lambda = 0 := by
    simp only [F, T, eval₂_comp, eval₂_mul, eval₂_C, eval₂_X, hy, eval₂_map, hcomp]
    rw [complex_value_at_real, hzero, Complex.ofReal_zero]
  exact cubic_nonvanishing_of_family (U := p6TwelveLayerRows) (by norm_num) (by norm_num)
    (by norm_num) p6TwelveLayer_actualFamily F hn hdegree hroot

end PiPolynomialValues
