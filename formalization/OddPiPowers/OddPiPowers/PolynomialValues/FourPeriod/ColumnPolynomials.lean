module

public import OddPiPowers.PolynomialValues.FourPeriod.Columns
public import OddPiPowers.PolynomialValues.FourPeriod.BandWidth
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Data.Finset.Max

/-! Group a dependence of the actual signed columns by frequency. The
original layer is the coefficient index, with the factor 2^j from the matrix. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

noncomputable def layerCoefficient {n : ℕ} (U : Fin n → ℕ) (a : Column U → ℂ)
    (t : ℤ) (j : Fin n) : ℂ :=
  if ht : t ∈ Finset.Icc (-(U j : ℤ)) (U j : ℤ) then 2^j.val * a ⟨j,t,ht⟩ else 0

noncomputable def columnPolynomial {n : ℕ} (U : Fin n → ℕ) (a : Column U → ℂ)
    (t : ℤ) : ℂ[X] := Polynomial.ofFn n (layerCoefficient U a t)

theorem columnPolynomial_coeff {n : ℕ} (U : Fin n → ℕ) (a : Column U → ℂ) (c : Column U) :
    (columnPolynomial U a c.2.val).coeff c.1.val = 2^c.1.val*a c := by
  obtain ⟨j,t,ht⟩ := c
  rw [columnPolynomial, ofFn_coeff_eq_val_of_lt _ j.isLt]
  simp [layerCoefficient, ht]

theorem columnPolynomial_coeff_outside {n : ℕ} (U : Fin n → ℕ) (hn : Antitone U)
    (a : Column U → ℂ) (t : ℤ) (j : Fin n) (ht : t ∉ Finset.Icc (-(U j : ℤ)) (U j : ℤ))
    {m : ℕ} (hm : j.val ≤ m) : (columnPolynomial U a t).coeff m = 0 := by
  by_cases h : m < n
  · let i : Fin n := ⟨m,h⟩
    have hi : U i ≤ U j := hn hm
    have hd : t ∉ Finset.Icc (-(U i : ℤ)) (U i : ℤ) := by
      intro hx
      apply ht
      obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [columnPolynomial, ofFn_coeff_eq_val_of_lt _ h]
    exact dif_neg hd
  · exact ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt h)

theorem columnPolynomial_inBand {n : ℕ} (U : Fin n → ℕ) (hn : Antitone U)
    (a : Column U → ℂ) (S : Finset ℤ) (j : Fin n) :
    InBand S (columnPolynomial U a) j.val (U j) := by
  intro t _ hder
  by_contra h
  have ht : t ∉ Finset.Icc (-(U j : ℤ)) (U j : ℤ) := fun hx => h (Finset.mem_Icc.mp hx)
  apply hder
  ext m
  rw [Polynomial.coeff_iterate_derivative, columnPolynomial_coeff_outside U hn a t j ht
    (Nat.le_add_left _ _), smul_zero, coeff_zero]

theorem exists_top_column {n : ℕ} (U : Fin n → ℕ) (a : Column U → ℂ) (ha : a ≠ 0) :
    ∃ c : Column U, a c ≠ 0 ∧ (columnPolynomial U a c.2.val).natDegree = c.1.val ∧
      (columnPolynomial U a c.2.val) ≠ 0 ∧ ∀ t : ℤ, (columnPolynomial U a t).natDegree ≤ c.1.val := by
  classical
  let cols := Finset.univ.filter (fun c : Column U => a c ≠ 0)
  have hne : cols.Nonempty := by
    by_contra h
    apply ha
    funext c
    by_contra hc
    exact h ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩⟩
  obtain ⟨c,hc,hmax⟩ := cols.exists_max_image (fun j => j.1.val) hne
  have hca : a c ≠ 0 := (Finset.mem_filter.mp hc).2
  have hdeg (t : ℤ) : (columnPolynomial U a t).natDegree ≤ c.1.val := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    by_cases h : m < n
    · let j : Fin n := ⟨m,h⟩
      rw [columnPolynomial, ofFn_coeff_eq_val_of_lt _ h]
      by_cases ht : t ∈ Finset.Icc (-(U j : ℤ)) (U j : ℤ)
      · let col : Column U := ⟨j,t,ht⟩
        have hz : a col = 0 := by
          by_contra H
          exact (Nat.not_le_of_gt hm) (hmax col (Finset.mem_filter.mpr ⟨Finset.mem_univ _,H⟩))
        change layerCoefficient U a t j = 0
        rw [layerCoefficient, dif_pos ht, show a ⟨j,t,ht⟩ = 0 from hz, mul_zero]
      · exact dif_neg ht
    · exact ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt h)
  have hcoeff : (columnPolynomial U a c.2.val).coeff c.1.val ≠ 0 := by
    rw [columnPolynomial_coeff]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hca
  exact ⟨c,hca,le_antisymm (hdeg _) (le_natDegree_of_ne_zero hcoeff),
    (fun h => hcoeff (by simp [h])),hdeg⟩

end PiPolynomialValues.FourPeriod
