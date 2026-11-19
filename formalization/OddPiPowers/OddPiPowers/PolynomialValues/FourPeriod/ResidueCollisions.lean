module

public import OddPiPowers.PolynomialValues.FourPeriod.PrimeLevels
public import Mathlib.Data.Int.Init
import Mathlib.Tactic.Ring

/-! Exact prefix floors and collision subtraction for arbitrary assignments
of the frequency columns to nodes and residue classes. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

def quotientSum (p m : ℕ) : ℤ := ∑ i ∈ range m, ((i / p : ℕ) : ℤ)

private theorem quotient_block (p h r : ℕ) (hp : 0 < p) (hr : r ≤ p) :
    quotientSum p (p*h+r) = quotientSum p (p*h) + (r : ℤ)*h := by
  simp only [quotientSum, sum_range_add]
  congr 1
  calc
    _ = ∑ _i ∈ range r, (h : ℤ) := by
      apply sum_congr rfl
      intro i hi
      have hi' : i < p := (mem_range.mp hi).trans_le hr
      rw [Nat.add_comm (p*h) i, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hi', zero_add]
    _ = _ := by simp

private theorem full_quotient_blocks (p h : ℕ) (hp : 0 < p) :
    2 * quotientSum p (p*h) = (p : ℤ)*h*((h : ℤ)-1) := by
  induction h with
  | zero => simp [quotientSum]
  | succ h ih =>
    rw [Nat.mul_succ, quotient_block p h p hp le_rfl, mul_add, ih, Nat.cast_succ]
    ring

theorem twice_quotientSum (p m : ℕ) (hp : 0 < p) :
    2 * quotientSum p m = collisionTwice m p := by
  have h := quotient_block p (m/p) (m%p) hp (Nat.mod_lt m hp).le
  rw [Nat.add_comm (p*(m/p)) (m%p), Nat.mod_add_div] at h
  rw [h, mul_add, full_quotient_blocks p (m/p) hp]
  simp only [collisionTwice, Int.natCast_div, Int.natCast_mod]
  ring

theorem row_collision_identity (p m : ℕ) (n : Fin p → ℕ) (hp : 0 < p)
    (hs : ∑ r, n r = m) :
    (∑ r, (n r : ℤ)*((n r : ℤ)-1)) - 2*quotientSum p m =
      ∑ r, ((n r : ℤ) - ↑(m/p)) * ((n r : ℤ) - ↑(m/p) - 1) := by
  let h : ℤ := ↑(m/p)
  let x : ℤ := ↑(m%p)
  have ht : (∑ r, (n r : ℤ)) = m := by exact_mod_cast hs
  have hm : (m : ℤ) = (p : ℤ)*h+x := by
    have e : m = p*(m/p) + m%p := by rw [add_comm, Nat.mod_add_div]
    simpa only [h, x, Nat.cast_add, Nat.cast_mul] using congrArg (fun a : ℕ => (a : ℤ)) e
  have e (r : Fin p) : (n r : ℤ)*((n r : ℤ)-1) =
      ((n r : ℤ)-h)*((n r : ℤ)-h-1) + (2*h*(n r : ℤ) - h*(h+1)) := by ring
  simp_rw [e]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ht, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, twice_quotientSum p m hp]
  change _ + (2*h*(m : ℤ) - (p : ℤ)*(h*(h+1))) -
    ((p : ℤ)*h*(h-1) + 2*x*h) = _
  rw [hm]
  ring

theorem residue_collision_sum_le {ι : Type*} (V : Finset ι) (p : ℕ) (hp : 0 < p)
    (m : ι → ℕ) (n : ι → Fin p → ℕ) (hrow : ∀ v ∈ V, ∑ r, n v r = m v) :
    (∑ r : Fin p, collisionTwice
      ((∑ v ∈ V, (n v r : ℤ)) - ∑ v ∈ V, ((m v / p : ℕ) : ℤ)) V.card) ≤
      ∑ v ∈ V, ((∑ r, (n v r : ℤ)*((n v r : ℤ)-1)) - 2*quotientSum p (m v)) := by
  let f (v : ι) (r : Fin p) : ℤ := (n v r : ℤ) - ↑(m v / p)
  calc
    _ = ∑ r : Fin p, collisionTwice (∑ v ∈ V, f v r) V.card := by
      simp only [f, sum_sub_distrib]
    _ ≤ ∑ r : Fin p, ∑ v ∈ V, f v r * (f v r-1) :=
      sum_le_sum (fun r _ => collisionTwice_le_actual V (fun v => f v r))
    _ = ∑ v ∈ V, ∑ r : Fin p, f v r * (f v r-1) := sum_comm
    _ = _ := sum_congr rfl (fun v hv => (row_collision_identity p (m v) (n v) hp (hrow v hv)).symm)

end PiPolynomialValues.FourPeriod
