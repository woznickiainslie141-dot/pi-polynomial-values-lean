module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Complex.Basic

/-! Pivoting at coefficient functionals in a finite-dimensional space of power series. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Module PowerSeries

/-- The first nonzero coefficient of a power series occurs at the displayed index. -/
def FirstCoefficient (p : PowerSeries ℂ) (m : ℕ) : Prop :=
  coeff m p ≠ 0 ∧ ∀ k < m, coeff k p = 0

private theorem exists_first_coefficient {p : PowerSeries ℂ} (hp : p ≠ 0) :
    ∃ m, FirstCoefficient p m := by
  classical
  have hex := exists_coeff_ne_zero_iff_ne_zero.mpr hp
  exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_not.mp (Nat.find_min hex hk)⟩

/-- An injectively represented n-dimensional space contains n series with
pairwise different first orders. Each induction step restricts the coefficient
map to the kernel of a nonzero linear functional. -/
theorem exists_distinct_first_coefficients (n : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (F : V →ₗ[ℂ] PowerSeries ℂ), Function.Injective F → finrank ℂ V = n →
      ∃ (x : Fin n → V) (m : Fin n → ℕ), Function.Injective m ∧
        ∀ i, FirstCoefficient (F (x i)) (m i) := by
  induction n with
  | zero =>
    intro V _ _ _ F hF hd
    exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro V _ _ _ F hF hd
    let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hd]; exact Nat.succ_pos n)
    obtain ⟨a, ha⟩ := exists_ne (0 : V)
    have hFa : F a ≠ 0 := fun h => ha (hF (h.trans (map_zero F).symm))
    obtain ⟨k, hk, hklo⟩ := exists_first_coefficient hFa
    let L := (coeff (R := ℂ) k).comp F
    have hL : L ≠ 0 := fun h => hk (show L a = 0 by rw [h, LinearMap.zero_apply])
    have hdim : finrank ℂ L.ker = n := by
      have h := Module.Dual.finrank_ker_add_one_of_ne_zero hL
      omega
    obtain ⟨x, m, hm, hx⟩ := ih (F.comp L.ker.subtype)
      (hF.comp Subtype.val_injective) hdim
    have hdist (i : Fin n) : m i ≠ k := by
      intro he
      have hh := (hx i).1
      rw [he] at hh
      exact hh ((x i).property)
    refine ⟨Fin.cons a (fun i => (x i : V)), Fin.cons k m, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · exact fun _ => rfl
        · exact fun h => (hdist j h.symm).elim
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · exact fun h => (hdist i h).elim
        · exact fun h => congrArg Fin.succ (hm h)
    · exact Fin.cases ⟨hk, hklo⟩ hx

end PiPolynomialValues.FourPeriod
