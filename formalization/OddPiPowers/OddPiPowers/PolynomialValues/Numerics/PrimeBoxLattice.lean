module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxArea
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The exact residue lattice in an open strip loses at most one point
from its real length, for each prime and for each of the two signs. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

noncomputable def openLattice (a b : ℝ) : Finset ℤ := Finset.Ioo ⌊a⌋ ⌈b⌉

theorem mem_openLattice (a b : ℝ) (j : ℤ) :
    j ∈ openLattice a b ↔ a < (j : ℝ) ∧ (j : ℝ) < b := by
  simp only [openLattice, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]

theorem openLattice_card_lower (a b : ℝ) :
    b-a-1 ≤ ((openLattice a b).card : ℝ) := by
  have h : ⌈b⌉-⌊a⌋-1 ≤ ((openLattice a b).card : ℤ) := by
    rw [openLattice, Int.card_Ioo]
    omega
  have h' : (⌈b⌉ : ℝ)-(⌊a⌋ : ℝ)-1 ≤ ((openLattice a b).card : ℝ) := by exact_mod_cast h
  linarith only [h', Int.floor_le a, Int.le_ceil b]

noncomputable def residuePoints (b : Box) (N p : ℕ) : Finset ℤ :=
  openLattice ((p : ℝ)*b.bottom.value ((N : ℝ)/p)) ((p : ℝ)*b.top.value ((N : ℝ)/p))

theorem mem_residuePoints (b : Box) (N p : ℕ) (hp : 0 < p) (j : ℤ) :
    j ∈ residuePoints b N p ↔
      b.bottom.value ((N : ℝ)/p) < (j : ℝ)/p ∧ (j : ℝ)/p < b.top.value ((N : ℝ)/p) := by
  have h : (0 : ℝ) < p := by exact_mod_cast hp
  simp only [residuePoints, mem_openLattice, lt_div_iff₀ h, div_lt_iff₀ h, mul_comm (p : ℝ)]

theorem residuePoints_card_lower (b : Box) (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    (N : ℝ)*stripWidth b ((p : ℝ)/N) - 1 ≤ ((residuePoints b N p).card : ℝ) := by
  have he : (p : ℝ)*b.top.value ((N : ℝ)/p) - (p : ℝ)*b.bottom.value ((N : ℝ)/p) =
      (N : ℝ)*stripWidth b ((p : ℝ)/N) := by
    unfold Boundary.value stripWidth
    field_simp [Nat.cast_ne_zero.mpr hN.ne', Nat.cast_ne_zero.mpr hp.ne'] <;> ring
  simpa only [residuePoints, he] using openLattice_card_lower
    ((p : ℝ)*b.bottom.value ((N : ℝ)/p)) ((p : ℝ)*b.top.value ((N : ℝ)/p))

end PiPolynomialValues.PrimeWindow
