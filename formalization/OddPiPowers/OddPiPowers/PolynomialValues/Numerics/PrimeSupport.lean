module

public import OddPiPowers.PolynomialValues.Numerics.PrimeShapeData
public import OddPiPowers.PolynomialValues.FourPeriod.PrimeSliceRate
public import Mathlib.Data.Nat.Prime.Factorial

/-! All primes of the selected denominator lie below the actual maximal
row mass plus a fixed padding. The product formula is exact on this set. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter PrimeWindow

def maxRowUnits (s : Shape) := s.rowUnits (s.rows.foldl max 0)
def primeCeiling (s : Shape) (t : ℕ) := maxRowUnits s*t + (s.widths.length+1)

private theorem member_le_fold (xs : List ℕ) (v z : ℕ) (hv : v ∈ xs) : v ≤ xs.foldl max z := by
  have hz (L : List ℕ) (n : ℕ) : n ≤ L.foldl max n := by
    induction L generalizing n with
    | nil => exact le_rfl
    | cons u us ih => exact (le_max_left n u).trans (ih (max n u))
  induction xs generalizing z with
  | nil => simp at hv
  | cons u us ih =>
    rcases List.mem_cons.mp hv with rfl|h
    · exact (le_max_right z v).trans (hz us (max z v))
    · exact ih _ h

theorem _root_.PiPolynomialValues.PrimeWindow.RowData.scan_le_ceiling {s : Shape} {g : List (List ℤ)} {K : ℕ}
    (D : RowData s g K) (t : ℕ) (v : Fin g.flatten.length) :
    scanRowCount s t (scannedNode g v) ≤ primeCeiling s t := by
  have h := member_le_fold s.rows (s.ratioAt (scannedNode g v)) 0 (D.ratio_mem v)
  unfold scanRowCount primeCeiling maxRowUnits Shape.rowUnits
  rw [Nat.mul_right_comm (2*s.widths.sum) t]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right t (Nat.mul_le_mul_left _ h)) _

theorem _root_.PiPolynomialValues.PrimeWindow.RowData.prime_support {s : Shape} {g : List (List ℤ)} {K t a b : ℕ} {y : ℂ}
    (D : RowData s g K) (w : SelectedPolynomial s g t y a b) :
    w.denominator.primeFactors ⊆ Nat.primesLE (primeCeiling s t) := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := (Nat.dvd_of_mem_primeFactors hp).trans w.denominator_dvd
  unfold rowFactorial at hd
  obtain ⟨i,_,hi⟩ := (hprime.prime.dvd_finsetProd_iff (fun i => (w.rows i).2.factorial)).mp hd
  have he := hprime.dvd_factorial.mp hi
  apply Nat.mem_primesLE.mpr
  exact ⟨he.trans ((w.rowIndex i).2.isLt.le.trans ((w.cap _).trans (D.scan_le_ceiling t _))),hprime⟩

theorem log_on_prime_support (B S : ℕ) (hB : 0 < B) (hs : B.primeFactors ⊆ Nat.primesLE S) :
    Real.log (B : ℝ) = ∑ p ∈ Nat.primesLE S, (B.factorization p : ℝ)*Real.log p := by
  calc
    _ = ∑ p ∈ B.primeFactors, (B.factorization p : ℝ)*Real.log p := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hB.ne']
      simp only [Nat.cast_prod,Nat.cast_pow]
      rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
      simp only [Real.log_pow]
    _ = _ := by
      apply sum_subset hs
      intro p hp hn
      have hz : B.factorization p = 0 := by
        have hprime := (Nat.mem_primesLE.mp hp).2
        exact Nat.factorization_eq_zero_of_not_dvd (fun h => hn (hprime.mem_primeFactors h hB.ne'))
      rw [hz,Nat.cast_zero,zero_mul]

theorem primeCeiling_eq (s : Shape) (t : ℕ) (hm : 0 < s.massUnit) :
    (primeCeiling s t : ℝ) = (s.largestRowQ : ℝ)*((s.massUnit*t : ℕ) : ℝ) + ((s.widths.length+1 : ℕ) : ℝ) := by
  simp only [primeCeiling,maxRowUnits,Shape.largestRowQ,Shape.rowMassQ,Rat.cast_div,Rat.cast_natCast,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  field_simp [Nat.cast_ne_zero.mpr hm.ne']

theorem eventually_prime_square (s : Shape) (hm : 0 < s.massUnit) (T : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ p : ℕ, 0 < p → s.massUnit*t ≤ T*p → 2 < p ∧ primeCeiling s t < p^2 := by
  let P := maxRowUnits s*T+s.widths.length+4
  filter_upwards [eventually_gt_atTop (T*P)] with t ht p hp hN
  have htp : t ≤ T*p := (show t ≤ s.massUnit*t by
    simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ s.massUnit from hm)).trans hN
  have hP : P < p := by
    by_contra! he
    exact ht.not_ge (htp.trans (Nat.mul_le_mul_left T he))
  have hpad : s.widths.length+1 ≤ (s.widths.length+1)*p := by simpa using Nat.mul_le_mul_left (s.widths.length+1) hp
  constructor
  · dsimp [P] at hP; omega
  · calc
      _ ≤ maxRowUnits s*(T*p)+(s.widths.length+1)*p := Nat.add_le_add (Nat.mul_le_mul_left _ htp) hpad
      _ = (maxRowUnits s*T+(s.widths.length+1))*p := by ring
      _ < p^2 := by
        rw [pow_two]
        apply Nat.mul_lt_mul_of_pos_right _ hp
        dsimp [P] at hP
        omega

end PiPolynomialValues.FourPeriod
