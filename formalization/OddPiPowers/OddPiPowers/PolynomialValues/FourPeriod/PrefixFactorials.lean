module

public import OddPiPowers.PolynomialValues.FourPeriod.ResidueCollisions
public import OddPiPowers.Arithmetic.LocalPrimeValuation

/-! Subtract the factorials in a complete prefix of derivative rows, using
the actual p-adic valuations at every prime above the square-root cutoff. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

theorem factorial_prefix_valuation {p : ℕ} [Fact p.Prime] (m : ℕ) (hm : m ≤ p*p) :
    (∑ j ∈ range m, (padicValNat p j.factorial : ℤ)) = quotientSum p m := by
  apply sum_congr rfl
  intro j hj
  rw [OddPiPowers.padicValNat_factorial_eq_div_of_lt_sq ((mem_range.mp hj).trans_le hm)]

theorem actual_factorial_collision_bound {ι : Type*} (V : Finset ι) (p : ℕ) [Fact p.Prime]
    (m : ι → ℕ) (n : ι → Fin p → ℕ) (hmax : ∀ v ∈ V, m v ≤ p*p)
    (hrow : ∀ v ∈ V, ∑ r, n v r = m v) :
    (∑ r : Fin p, collisionTwice
      ((∑ v ∈ V, (n v r : ℤ)) - ∑ v ∈ V, ((m v / p : ℕ) : ℤ)) V.card) ≤
      ∑ v ∈ V, ((∑ r, (n v r : ℤ)*((n v r : ℤ)-1)) -
        2*∑ j ∈ range (m v), (padicValNat p j.factorial : ℤ)) := by
  apply (residue_collision_sum_le V p (Fact.out : Nat.Prime p).pos m n hrow).trans_eq
  apply sum_congr rfl
  intro v hv
  rw [factorial_prefix_valuation (m v) (hmax v hv)]

end PiPolynomialValues.FourPeriod
