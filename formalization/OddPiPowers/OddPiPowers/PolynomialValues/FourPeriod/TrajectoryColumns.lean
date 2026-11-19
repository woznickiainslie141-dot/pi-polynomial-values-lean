module

public import OddPiPowers.PolynomialValues.FourPeriod.ExponentialIndependence

/-! On the exponential trajectory, the formal derivatives in the second
variable give independent columns as soon as one frequency has full degree. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

theorem derivative_columns_independent {J : ℕ} (p : ℂ[X]) (hp : p ≠ 0)
    (hd : p.natDegree = J) :
    LinearIndependent ℂ (fun k : Fin (J + 1) => Polynomial.derivative^[k.val] p) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  suffices hall : ∀ k, ∀ hk : k < J + 1, a ⟨k, hk⟩ = 0 from fun i => hall i.val i.isLt
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    let i : Fin (J + 1) := ⟨k, hk⟩
    have hkJ : k ≤ J := by omega
    have hc := congrArg (fun q : ℂ[X] => q.coeff (J - k)) ha
    simp only [finsetSum_coeff, coeff_smul, coeff_zero, smul_eq_mul] at hc
    rw [Finset.sum_eq_single i] at hc
    · have hg : (Polynomial.derivative^[k] p).coeff (J - k) ≠ 0 := by
        rw [coeff_iterate_derivative, Nat.sub_add_cancel hkJ, nsmul_eq_mul]
        apply mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hkJ).ne')
        rw [← hd, coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hp
      exact (mul_eq_zero.mp hc).resolve_right hg
    · intro j _ hji
      by_cases hj : j.val < k
      · rw [ih j.val hj j.isLt, zero_mul]
      · have hne : j.val ≠ k := fun h => hji (Fin.ext h)
        rw [coeff_iterate_derivative, coeff_eq_zero_of_natDegree_lt
          (show p.natDegree < J - k + j.val by omega), smul_zero, mul_zero]
    · simp

noncomputable def trajectoryColumn (S : Finset ℤ) (p : ℤ → ℂ[X]) (k : ℕ) : PowerSeries ℂ :=
  ∑ t ∈ S, frequencyExp (t : ℂ) * ((Polynomial.derivative^[k] (p t) : ℂ[X]) : PowerSeries ℂ)

theorem trajectory_columns_independent {J : ℕ} (S : Finset ℤ) (p : ℤ → ℂ[X])
    {t₀ : ℤ} (ht : t₀ ∈ S) (hp : p t₀ ≠ 0) (hd : (p t₀).natDegree = J) :
    LinearIndependent ℂ (fun k : Fin (J + 1) => trajectoryColumn S p k.val) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  let q (t : ℤ) := ∑ k : Fin (J + 1), a k • (Polynomial.derivative^[k.val] (p t))
  have hq : (∑ t ∈ S, frequencyExp (t : ℂ) * (q t : PowerSeries ℂ)) = 0 := by
    calc
      _ = ∑ k : Fin (J + 1), ∑ t ∈ S, a k • (frequencyExp (t : ℂ) *
          ((Polynomial.derivative^[k.val] (p t) : ℂ[X]) : PowerSeries ℂ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        change frequencyExp (t : ℂ) * Polynomial.coeToPowerSeries.ringHom (∑ k : Fin (J + 1), _) = _
        simp only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_smul,
          Finset.mul_sum, mul_smul_comm]
      _ = _ := by simpa only [trajectoryColumn, Finset.smul_sum] using ha
  exact Fintype.linearIndependent_iff.mp (derivative_columns_independent (p t₀) hp hd) a
    ((exp_polynomial_sum_eq_zero_iff S q).mp hq t₀ ht)

end PiPolynomialValues.FourPeriod
