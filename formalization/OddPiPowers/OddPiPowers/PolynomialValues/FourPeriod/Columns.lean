module

public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.Pairwise

/-! The finite set of labeled signed frequencies on a nested integer band. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

abbrev Column {n : ℕ} (U : Fin n → ℕ) :=
  (j : Fin n) × ↥(Finset.Icc (-(U j : ℤ)) (U j : ℤ))

def columnLabel {n : ℕ} {U : Fin n → ℕ} (c : Column U) : ℤ × ℕ := (c.2.val, c.1.val)

theorem columnLabel_injective {n : ℕ} (U : Fin n → ℕ) :
    Function.Injective (columnLabel (U := U)) := by
  rintro ⟨j, t⟩ ⟨k, s⟩ h
  have hj : j = k := Fin.ext (congrArg Prod.snd h)
  subst k
  exact congrArg (Sigma.mk j) (Subtype.ext (congrArg Prod.fst h))

theorem column_card {n : ℕ} (U : Fin n → ℕ) :
    Fintype.card (Column U) = ∑ j, (2 * U j + 1) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.card_coe, Int.card_Icc]
  omega

/-- The preceding layer contains this same signed frequency. -/
def previousColumn {n : ℕ} {U : Fin n → ℕ} (h : Antitone U) (c : Column U) : Column U :=
  let j : Fin n := ⟨c.1.val - 1, (Nat.sub_le _ _).trans_lt c.1.isLt⟩
  let hj : U c.1 ≤ U j := h (show j ≤ c.1 from Nat.sub_le _ _)
  ⟨j, c.2.val, Finset.mem_Icc.mpr (by
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp c.2.property
    omega)⟩

theorem previousColumn_label {n : ℕ} {U : Fin n → ℕ} (h : Antitone U) (c : Column U)
    (j : ℕ) (hj : (columnLabel c).2 = j + 1) :
    columnLabel (previousColumn h c) = ((columnLabel c).1, j) := by
  change (c.2.val, c.1.val - 1) = (c.2.val, j)
  change c.1.val = j + 1 at hj
  rw [hj, Nat.add_sub_cancel]

def Shape.band (s : Shape) (t : ℕ) (j : Fin s.widths.length) : ℕ :=
  s.widths.get j * s.rows.sum * t

private theorem band_antitone {s : Shape} (hs : s.widths.Pairwise (· ≥ ·)) (t : ℕ) :
    Antitone (s.band t) := fun _ _ h =>
  Nat.mul_le_mul_right t (Nat.mul_le_mul_right s.rows.sum (hs.rel_get_of_le h))

theorem quadratic_bands_nested (t : ℕ) : Antitone (quadraticShape.band t) :=
  band_antitone (s := quadraticShape) (by decide +kernel) t

theorem cubic_bands_nested (t : ℕ) : Antitone (cubicShape.band t) :=
  band_antitone (s := cubicShape) (by decide +kernel) t

theorem shape_column_card (s : Shape) (t : ℕ) :
    Fintype.card (Column (s.band t)) = 2 * s.widths.sum * s.rows.sum * t + s.widths.length := by
  rw [column_card, Finset.sum_add_distrib]
  have hw : (∑ j, s.widths.get j) = s.widths.sum := by
    rw [← Fin.sum_ofFn, List.ofFn_get]
  simp only [Shape.band, ← Finset.mul_sum, ← Finset.sum_mul, hw, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  simp only [Nat.mul_assoc]

end PiPolynomialValues.FourPeriod
