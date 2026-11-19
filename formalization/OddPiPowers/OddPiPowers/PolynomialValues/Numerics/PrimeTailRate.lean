module

public import OddPiPowers.PolynomialValues.FourPeriod.PrimeSliceRate
public import OddPiPowers.PolynomialValues.Numerics.PrimeTailSound

/-! The prime number theorem evaluates the signed ramp certificate on
its actual interval at each retained level. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter
open scoped Topology Interval

theorem primeAverage_linear (l r a b : ℝ) (f g : ℝ → ℝ) (N : ℕ) :
    primeAverage l r (fun x => a*f x+b*g x) N =
      a*primeAverage l r f N + b*primeAverage l r g N := by
  unfold primeAverage
  simp only [add_mul,mul_assoc,sum_add_distrib,← mul_sum]
  ring

theorem listTail_prime_rate (es : List TailTerm) (h : ℕ) {l r : ℚ} (hl : 0 < l) (hlr : l ≤ r) :
    Tendsto (primeAverage l r (listTail es h)) atTop (𝓝 (((es.map (fun e => e.area h l r)).sum : ℚ) : ℝ)) := by
  induction es with
  | nil =>
    have he : primeAverage l r (listTail [] h) = fun _ : ℕ => 0 := by
      funext N
      simp [primeAverage,listTail]
    rw [he]
    simpa only [List.map_nil,List.sum_nil,Rat.cast_zero] using (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop (α := ℕ)))
  | cons e es ih =>
    have hr : Tendsto (primeAverage l r (e.value h)) atTop (𝓝 (e.area h l r : ℝ)) := by
      rw [← e.integral_value h l r hlr]
      exact primeSlice_ramp (by exact_mod_cast hl) (by exact_mod_cast hlr) _ _ (Nat.cast_nonneg _)
    rw [List.map_cons,List.sum_cons,Rat.cast_add]
    apply (hr.add ih).congr
    intro N
    change _ = primeAverage l r (fun x => e.value h x+listTail es h x) N
    simpa only [one_mul] using (primeAverage_linear l r 1 1 (e.value h) (listTail es h) N).symm

theorem Shape.netTail_prime_rate (s : Shape) (h : ℕ) {l r : ℚ} (hl : 0 < l) (hlr : l ≤ r) :
    Tendsto (primeAverage l r (s.netTailValue h)) atTop (𝓝 (s.netTailIntegral h l r : ℝ)) := by
  let A : ℝ := 4/(s.totalWidthQ : ℝ)
  let B : ℝ := -1/(s.totalWidthQ : ℝ)
  have h₁ := (listTail_prime_rate s.columnTails h hl hlr).const_mul A
  have h₂ := (listTail_prime_rate s.rowTails h hl hlr).const_mul B
  have he : s.netTailValue h = fun x => A*listTail s.columnTails h x+B*listTail s.rowTails h x := by
    funext x
    unfold Shape.netTailValue A B
    ring
  rw [he]
  have h₃ := (h₁.add h₂).congr (fun N => (primeAverage_linear _ _ A B _ _ N).symm)
  convert h₃ using 2
  unfold Shape.netTailIntegral A B
  push_cast
  ring

end PiPolynomialValues.FourPeriod
