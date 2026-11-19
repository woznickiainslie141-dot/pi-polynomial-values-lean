module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite level savings for a single matching in the Gaussian coefficient
matrix, and the discrete quadratic collision cost used in the lifted prime windows. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def countAbove {ι : Type*} (S : Finset ι) (u : ι → ℕ) (h : ℕ) : ℕ :=
  ∑ i ∈ S, if h < u i then 1 else 0

private theorem level_deficit {ι : Type*} (S : Finset ι) (u v : ι → ℕ) (h : ℕ) :
    countAbove S u h - countAbove S v h ≤ ∑ i ∈ S, if v i ≤ h ∧ h < u i then 1 else 0 := by
  apply Nat.sub_le_of_le_add
  rw [countAbove, countAbove, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> omega

theorem total_level_saving {ι : Type*} (S : Finset ι) (u v : ι → ℕ) (N : ℕ)
    (hu : ∀ i ∈ S, u i ≤ N) :
    ∑ h ∈ Finset.range N, (countAbove S u h - countAbove S v h) ≤ ∑ i ∈ S, (u i - v i) := by
  calc
    _ ≤ ∑ h ∈ Finset.range N, ∑ i ∈ S, if v i ≤ h ∧ h < u i then 1 else 0 :=
      Finset.sum_le_sum fun h _ => level_deficit S u v h
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      have hs : (Finset.range N).filter (fun h => v i ≤ h ∧ h < u i) = Finset.Ico (v i) (u i) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        have := hu i hi
        omega
      simp [Finset.sum_boole, hs]

/-- The matched entry loses exactly the surplus of its row level over its
column level from the floor-difference bound. -/
theorem matched_prime_cost (a b j q : ℕ) (hab : b ≤ a) (hqj : q ≤ j) :
    min (j - q) (a - b) + (a + q - (j + b)) = a - b := by omega

private theorem convex_integer_cost (x q : ℤ) :
    2 * q * x - q * (q + 1) ≤ x * (x - 1) := by
  have h : 0 ≤ (x - q) * (x - q - 1) := by
    by_cases hx : x ≤ q
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  nlinarith only [h]

/-- Applies to signed lifts, including the deficient residue tail. The bound
is exact when every lift count equals q or q+1. The expression is twice the
integer cost, so no division or rounding occurs in this statement. -/
theorem signed_lift_cost {ι : Type*} (S : Finset ι) (x : ι → ℤ) (q r : ℤ)
    (hs : ∑ i ∈ S, x i = (S.card : ℤ) * q + r) :
    (S.card : ℤ) * q * (q - 1) + 2 * r * q ≤ ∑ i ∈ S, x i * (x i - 1) := by
  have h := Finset.sum_le_sum (s := S) (fun i _ => convex_integer_cost (x i) q)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, Finset.sum_const, nsmul_eq_mul] at h
  calc
    _ = 2 * q * ((S.card : ℤ) * q + r) - (S.card : ℤ) * (q * (q + 1)) := by ring
    _ ≤ _ := h

theorem reflected_lift_cost (x : ℤ) : (1 - x) * ((1 - x) - 1) = x * (x - 1) := by ring

/-- Twice the minimum total collision cost for M signed integer counts of sum x. -/
def collisionTwice (x M : ℤ) : ℤ :=
  let k := x / M
  M * k * (k - 1) + 2 * (x % M) * k

theorem dual_le_collisionTwice (x M q : ℤ) (hM : 0 < M) :
    2 * q * x - M * q * (q + 1) ≤ collisionTwice x M := by
  let k := x / M
  let r := x % M
  have hx : x = M * k + r := (Int.mul_ediv_add_emod x M).symm
  have hr : 0 ≤ r := Int.emod_nonneg x hM.ne'
  have hrM : r < M := Int.emod_lt_of_pos x hM
  have hlo := mul_le_mul_of_nonneg_left (convex_integer_cost k q) (sub_nonneg.mpr hrM.le)
  have hhi := mul_le_mul_of_nonneg_left (convex_integer_cost (k+1) q) hr
  calc
    2 * q * x - M * q * (q + 1) =
        (M-r) * (2*q*k - q*(q+1)) + r * (2*q*(k+1) - q*(q+1)) := by
      conv_lhs => rw [hx]
      ring
    _ ≤ (M-r) * (k*(k-1)) + r * ((k+1)*((k+1)-1)) := add_le_add hlo hhi
    _ = collisionTwice x M := by change _ = M*k*(k-1) + 2*r*k; ring

theorem collisionTwice_nonneg (x M : ℤ) (hM : 0 < M) : 0 ≤ collisionTwice x M := by
  simpa using dual_le_collisionTwice x M 0 hM

theorem collisionTwice_le_actual {ι : Type*} (S : Finset ι) (n : ι → ℤ) :
    collisionTwice (∑ i ∈ S, n i) S.card ≤ ∑ i ∈ S, n i * (n i - 1) := by
  let x := ∑ i ∈ S, n i
  exact signed_lift_cost S n (x / (S.card : ℤ)) (x % (S.card : ℤ))
    (Int.mul_ediv_add_emod x (S.card : ℤ)).symm

end PiPolynomialValues.FourPeriod
