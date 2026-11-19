module

public import OddPiPowers.PolynomialValues.FourPeriod.ProgressionFloors
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Integer monic Newton rows on a progression. All prime powers dividing
the row factorial survive differentiation except for a uniform loss per derivative. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

noncomputable def newtonRow (step : ℕ) (a : ℤ) (m : ℕ) : ℤ[X] :=
  ∏ i ∈ range m, (X+C (a-(step : ℤ)*i))

theorem newtonRow_monic (step : ℕ) (a : ℤ) (m : ℕ) : (newtonRow step a m).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

theorem newtonRow_degree (step : ℕ) (a : ℤ) (m : ℕ) : (newtonRow step a m).natDegree = m := by
  rw [newtonRow,natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C,sum_const,card_range,nsmul_eq_mul,mul_one,Nat.cast_id]

theorem newtonRow_prime_derivative (p step m L j : ℕ) (a x : ℤ) (hp : p.Prime)
    (hc : step.Coprime p) (hL : p.log m ≤ L) :
    (p : ℤ)^(m.factorial.factorization p-L*j) ∣
      ((derivative^[j]) (newtonRow step a m)).eval x := by
  let w (i : ℕ) := trackedPowers p L (x+a-(step : ℤ)*i)
  let f (i : ℕ) : ℤ[X] := X+C (a-(step : ℤ)*i)
  have hval (i : ℕ) : (f i).eval x = x+a-(step : ℤ)*i := by simp [f]; ring
  have hd := weighted_integer_poly_product (range m) f w p x L j
    (fun i _ => trackedPowers_le _ _ _) (fun i _ => by rw [hval]; exact trackedPowers_dvd _ _ _)
  have hsum := factorial_le_tracked p step m L (x+a) hp hc hL
  exact (pow_dvd_pow (p : ℤ) (Nat.sub_le_sub_right hsum _)).trans hd

theorem newtonRow_succ_right (step : ℕ) (a : ℤ) (m : ℕ) :
    newtonRow step a (m+1) = newtonRow step a m * (X+C (a-(step : ℤ)*m)) := by
  exact prod_range_succ _ _

theorem newtonRow_shift_succ (step : ℕ) (a : ℤ) (m : ℕ) :
    newtonRow step (a+step) (m+1) = newtonRow step a m * (X+C (a+step)) := by
  rw [newtonRow,prod_range_succ']
  simp only [Nat.cast_zero,mul_zero,sub_zero]
  congr 1
  apply prod_congr rfl
  intro i _
  congr 2
  push_cast
  ring

theorem newtonRow_step (step : ℕ) (a : ℤ) (m : ℕ) :
    newtonRow step (a+step) (m+1) - newtonRow step a (m+1) =
      C (((m+1 : ℕ) : ℤ)*step) * newtonRow step a m := by
  rw [newtonRow_shift_succ,newtonRow_succ_right]
  simp only [Nat.cast_succ,map_add,map_sub,map_mul,map_one]
  ring

theorem newtonRow_comp_shift (step : ℕ) (a h : ℤ) (m : ℕ) :
    (newtonRow step a m).comp (X+C h) = newtonRow step (a+h) m := by
  induction m with
  | zero => simp [newtonRow]
  | succ m ih =>
    rw [newtonRow_succ_right,newtonRow_succ_right,mul_comp,ih,add_comp,X_comp,C_comp]
    simp only [map_add,map_sub,map_mul]
    ring

end PiPolynomialValues.FourPeriod
