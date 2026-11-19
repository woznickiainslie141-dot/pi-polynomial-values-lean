module

public import OddPiPowers.PolynomialValues.FourPeriod.Degree

/-! At a fixed order and residue, the coefficient of each power of the
argument is a common row multiplied by the same power of the signed node. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial OddPiPowers

noncomputable def frequencyKernel (t : ℤ) (σ j : ℕ) : GaussianInt[X] :=
  (rowOperator (2 : GaussianInt[X]) (C gaussianI * X) j (X ^ σ)).eval (C (t : GaussianInt))

theorem rawEntry_comp_node (v t : ℤ) (σ j : ℕ) :
    rawEntry v t σ j = C (phase (v*t)) * (frequencyKernel t σ j).comp (C (v : GaussianInt) * X) := by
  let φ := eval₂RingHom (C : GaussianInt →+* GaussianInt[X]) (C (v : GaussianInt) * X)
  have hu : φ (C gaussianI * X) = nodeCoefficient v := by
    simp only [φ, map_mul, coe_eval₂RingHom, eval₂_C, eval₂_X, nodeCoefficient]
    ring
  have ht : φ (C (t : GaussianInt)) = C (t : GaussianInt) := by
    simp only [φ, coe_eval₂RingHom, eval₂_C]
  unfold rawEntry
  congr 1
  symm
  change φ ((rowOperator _ _ _ _).eval (C (t : GaussianInt))) = _
  rw [← eval_map_apply, map_rowOperator, hu, ht, map_ofNat, Polynomial.map_pow, map_X]

noncomputable def originCoefficient (r : ℤ) (σ h : ℕ) (t : ℤ) (j : ℕ) : GaussianInt :=
  phase (r*t) * (frequencyKernel t σ j).coeff h

theorem rawEntry_coeff_node (v t : ℤ) (σ j h : ℕ) :
    (rawEntry v t σ j).coeff h = (v : GaussianInt)^h * originCoefficient (v%4) σ h t j := by
  rw [rawEntry_comp_node, coeff_C_mul, comp_C_mul_X_coeff]
  have he : phase (v*t) = phase ((v%4)*t) := by
    unfold phase
    rw [Int.mul_emod v t, Int.mul_emod (v%4) t, Int.emod_emod]
  rw [he]
  unfold originCoefficient
  ring

theorem rawEntry_expansion (v t : ℤ) (σ j m : ℕ) (hj : j < m) :
    rawEntry v t σ j = ∑ h : Fin m, (C ((v : GaussianInt)^h.val) * X^h.val) *
      C (originCoefficient (v%4) σ h.val t j) := by
  let term (h : ℕ) := C ((rawEntry v t σ j).coeff h) * X^h
  calc
    _ = ∑ h ∈ Finset.range m, term h :=
      (rawEntry v t σ j).as_sum_range_C_mul_X_pow' ((rawEntry_degree v t σ j).trans_lt hj)
    _ = ∑ h : Fin m, term h.val := (Fin.sum_univ_eq_sum_range term m).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [term, rawEntry_coeff_node, map_mul]
      ring

end PiPolynomialValues.FourPeriod
