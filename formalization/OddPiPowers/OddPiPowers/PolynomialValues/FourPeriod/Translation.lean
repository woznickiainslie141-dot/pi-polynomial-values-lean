module

public import OddPiPowers.PolynomialValues.FourPeriod.LocalWronskian
public import OddPiPowers.PolynomialValues.FourPeriod.TrajectoryColumns
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots

/-! Translation in z is exactly the constant change of derivative columns
at one fourth root of unity. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

theorem polynomial_translation {J : ℕ} (p : ℂ[X]) (hd : p.natDegree ≤ J) (a : ℂ) :
    Polynomial.taylor a p = ∑ k : Fin (J + 1),
      (a ^ k.val / (k.val.factorial : ℂ)) • (Polynomial.derivative^[k.val] p) := by
  apply Polynomial.funext
  intro z
  have h : (Polynomial.taylor z p).natDegree < J + 1 := by
    rw [natDegree_taylor]
    exact Nat.lt_succ_of_le hd
  rw [taylor_eval, add_comm z a, ← taylor_eval z p a, eval_eq_sum_range' h,
    ← Fin.sum_univ_eq_sum_range, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  have hdif : Polynomial.derivative^[k.val] p =
      k.val.factorial • Polynomial.hasseDeriv k.val p := by
    simpa only [Pi.smul_apply, LinearMap.smul_apply] using
      (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := k.val)) p).symm
  rw [taylor_coeff, hdif, nsmul_eq_mul, eval_smul, eval_mul, eval_natCast, smul_eq_mul]
  have hn : (k.val.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

noncomputable def localColumn (ρ : ℂ) (S : Finset ℤ) (p : ℤ → ℂ[X]) (k : ℕ) : PowerSeries ℂ :=
  ∑ t ∈ S, ρ ^ t • (frequencyExp (t : ℂ) *
    ((Polynomial.derivative^[k] (p t) : ℂ[X]) : PowerSeries ℂ))

noncomputable def translatedTrajectory (ρ a : ℂ) (S : Finset ℤ) (p : ℤ → ℂ[X]) :
    PowerSeries ℂ :=
  ∑ t ∈ S, ρ ^ t • (frequencyExp (t : ℂ) * ((Polynomial.taylor a (p t)) : PowerSeries ℂ))

theorem mix_localColumn {J : ℕ} (ρ : ℂ) (S : Finset ℤ) (p : ℤ → ℂ[X])
    (hd : ∀ t ∈ S, (p t).natDegree ≤ J) (a : Fin (J + 1) → ℂ) (j : Fin (J + 1)) :
    mixColumn (translationMatrix a) (fun k => localColumn ρ S p k.val) j =
      translatedTrajectory ρ (a j) S p := by
  unfold mixColumn localColumn translatedTrajectory
  simp only [translationMatrix, Matrix.of_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [polynomial_translation (p t) (hd _ ht)]
  change _ = ρ ^ t • (frequencyExp (t : ℂ) *
    Polynomial.coeToPowerSeries.ringHom (∑ k : Fin (J + 1), _))
  simp only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_smul,
    Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact smul_comm _ _ _

end PiPolynomialValues.FourPeriod
