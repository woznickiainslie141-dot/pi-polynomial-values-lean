module

public import OddPiPowers.PolynomialValues.FourPeriod.IntegerMatrix
public import Mathlib.LinearAlgebra.Span.Basic

/-! Multiplication by the frequency is one linear operator on every
specialized row. Greedy rejection propagates along each node's row prefix. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

noncomputable def frequencyShift {κ : Type*} (cols : κ → ℤ × ℕ) (pred : κ → κ) :
    (κ → ℂ) →ₗ[ℂ] (κ → ℂ) where
  toFun x c := ((cols c).1 : ℂ) * x c + ((cols c).2 : ℂ) * 2 * x (pred c)
  map_add' x y := by funext c; simp only [Pi.add_apply]; ring
  map_smul' a x := by funext c; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; ring

noncomputable def specializedRow {κ : Type*} (cols : κ → ℤ × ℕ) (v : ℤ) (σ : ℕ) (ξ : ℂ) :
    κ → ℂ := fun c => (rawEntry v (cols c).1 σ (cols c).2).eval₂ GaussianInt.toComplex ξ

theorem frequencyShift_row {κ : Type*} (cols : κ → ℤ × ℕ) (pred : κ → κ)
    (hp : ∀ c j, (cols c).2 = j + 1 → cols (pred c) = ((cols c).1, j))
    (v : ℤ) (σ : ℕ) (ξ : ℂ) :
    frequencyShift cols pred (specializedRow cols v σ ξ) = specializedRow cols v (σ + 1) ξ := by
  funext c
  have hcast (t : ℤ) : (t : GaussianInt[X]).eval₂ GaussianInt.toComplex ξ = (t : ℂ) :=
    map_intCast (eval₂RingHom GaussianInt.toComplex ξ) t
  cases hj : (cols c).2 with
  | zero =>
    simp only [frequencyShift, specializedRow, LinearMap.coe_mk, AddHom.coe_mk, hj,
      rawEntry_shift_zero, eval₂_mul, eval₂_C, map_intCast, hcast, Nat.cast_zero, zero_mul, add_zero]
  | succ j =>
    have hprev := hp c j hj
    simp only [frequencyShift, specializedRow, LinearMap.coe_mk, AddHom.coe_mk, hj, hprev,
      rawEntry_shift_succ, eval₂_add, eval₂_mul, eval₂_C, eval₂_natCast, eval₂_ofNat, map_intCast, hcast]

/-- Smaller keys give all the rows that a greedy scan has already visited.
Delays translate the different nodes' desired row counts into a common clock. -/
def scanKey {V : ℕ} (delay : Fin V → ℕ) (v : Fin V) (k : ℕ) : ℕ := (delay v + k) * V + v.val

theorem scanKey_succ {V : ℕ} (delay : Fin V → ℕ) (v : Fin V) (k : ℕ) :
    scanKey delay v (k + 1) = scanKey delay v k + V := by unfold scanKey; ring

noncomputable def earlierRows {κ : Type*} {V : ℕ} (delay : Fin V → ℕ)
    (row : Fin V → ℕ → κ → ℂ) (s : ℕ) : Submodule ℂ (κ → ℂ) :=
  Submodule.span ℂ {x | ∃ v k, scanKey delay v k < s ∧ x = row v k}

def rowKept {κ : Type*} {V : ℕ} (delay : Fin V → ℕ) (row : Fin V → ℕ → κ → ℂ)
    (v : Fin V) (k : ℕ) : Prop := row v k ∉ earlierRows delay row (scanKey delay v k)

theorem earlierRows_shift {κ : Type*} {V : ℕ} (delay : Fin V → ℕ)
    (row : Fin V → ℕ → κ → ℂ) (T : (κ → ℂ) →ₗ[ℂ] (κ → ℂ))
    (hT : ∀ v k, T (row v k) = row v (k + 1)) (s : ℕ) :
    earlierRows delay row s ≤ (earlierRows delay row (s + V)).comap T := by
  apply Submodule.span_le.mpr
  rintro x ⟨v, k, hk, rfl⟩
  change T (row v k) ∈ earlierRows delay row (s + V)
  rw [hT]
  exact Submodule.subset_span ⟨v, k + 1, by simpa only [scanKey_succ] using Nat.add_lt_add_right hk V, rfl⟩

theorem rowKept_of_succ {κ : Type*} {V : ℕ} (delay : Fin V → ℕ)
    (row : Fin V → ℕ → κ → ℂ) (T : (κ → ℂ) →ₗ[ℂ] (κ → ℂ))
    (hT : ∀ v k, T (row v k) = row v (k + 1)) (v : Fin V) (k : ℕ)
    (hk : rowKept delay row v (k + 1)) : rowKept delay row v k := by
  intro h
  apply hk
  rw [scanKey_succ, ← hT]
  exact earlierRows_shift delay row T hT _ h

theorem rowKept_initial_segment {κ : Type*} {V : ℕ} (delay : Fin V → ℕ)
    (row : Fin V → ℕ → κ → ℂ) (T : (κ → ℂ) →ₗ[ℂ] (κ → ℂ))
    (hT : ∀ v k, T (row v k) = row v (k + 1)) (v : Fin V) {k l : ℕ}
    (hkl : k ≤ l) (hl : rowKept delay row v l) : rowKept delay row v k := by
  induction hkl with
  | refl => exact hl
  | step h ih => exact ih (rowKept_of_succ delay row T hT v _ hl)

theorem keptRows_span {κ : Type*} {V : ℕ} (delay : Fin V → ℕ)
    (row : Fin V → ℕ → κ → ℂ) (s : ℕ) :
    earlierRows delay row s =
      Submodule.span ℂ {x | ∃ v k, scanKey delay v k < s ∧ rowKept delay row v k ∧ x = row v k} := by
  let W := Submodule.span ℂ {x | ∃ v k, scanKey delay v k < s ∧ rowKept delay row v k ∧ x = row v k}
  apply le_antisymm _ (Submodule.span_mono (by rintro x ⟨v, k, h, _, rfl⟩; exact ⟨v, k, h, rfl⟩))
  apply Submodule.span_le.mpr
  have all (n : ℕ) : ∀ v k, scanKey delay v k = n → n < s → row v k ∈ W := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v k hk hs
      by_cases hkeep : rowKept delay row v k
      · exact Submodule.subset_span ⟨v, k, hk.symm ▸ hs, hkeep, rfl⟩
      · have hr : row v k ∈ earlierRows delay row (scanKey delay v k) := by
          simpa only [rowKept, not_not] using hkeep
        apply (show earlierRows delay row (scanKey delay v k) ≤ W from ?_) hr
        apply Submodule.span_le.mpr
        rintro x ⟨w, l, hlt, rfl⟩
        rw [hk] at hlt
        exact ih _ hlt w l rfl (hlt.trans hs)
  rintro x ⟨v, k, hk, rfl⟩
  exact all _ v k rfl hk

end PiPolynomialValues.FourPeriod
