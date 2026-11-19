module

public import OddPiPowers.PolynomialValues.Analysis.PathDerivativeRows

/-! Taylor expansions of divided rows through a common column degree.
The coefficient indexed by k uses the k-th derivative of the original
column, independently of the row from which it was obtained. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

theorem analytic_iterated_at_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    AnalyticAt ℂ (iteratedDeriv k f) 0 := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem iteratedDeriv_after (f : ℂ → ℂ) (s k : ℕ) :
    iteratedDeriv k (iteratedDeriv s f) = iteratedDeriv (s+k) f := by
  simp only [iteratedDeriv_eq_iterate]
  rw [Nat.add_comm,Function.iterate_add_apply]

noncomputable def jetCoefficient (s k : ℕ) : ℂ :=
  if s ≤ k then (s.factorial : ℂ)⁻¹*((k-s).factorial : ℂ)⁻¹ else 0

theorem dividedTaylor {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (σ K : ℕ) (hσ : σ ≤ K) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ z : ℂ, dividedRow σ f z =
      (∑ k ∈ range K, iteratedDeriv k f 0*jetCoefficient σ k*z^(k-σ))+z^(K-σ)*R z := by
  obtain ⟨g,hg,he⟩ := (analytic_iterated_at_zero hf σ).exists_eq_sum_add_pow_mul (K-σ)
  refine ⟨fun z => (σ.factorial : ℂ)⁻¹*g z,analyticAt_const.mul hg,?_⟩
  intro z
  let term (k : ℕ) := iteratedDeriv k f 0*jetCoefficient σ k*z^(k-σ)
  have hsplit : (∑ k ∈ range K, term k) = ∑ i ∈ range (K-σ), term (σ+i) := by
    have h := sum_range_add term σ (K-σ)
    rw [Nat.add_sub_of_le hσ] at h
    have h0 : (∑ i ∈ range σ, term i)=0 := sum_eq_zero fun i hi => by
      simp [term,jetCoefficient,not_le_of_gt (mem_range.mp hi)]
    rwa [h0,zero_add] at h
  change _ = (∑ k ∈ range K, term k)+_
  rw [hsplit,dividedRow,he,mul_add,mul_sum]
  simp only [smul_eq_mul,iteratedDeriv_after,term,jetCoefficient,Nat.le_add_right,if_true,
    Nat.add_sub_cancel_left]
  congr 1
  · apply sum_congr rfl
    intro i _
    ring
  · ring

end PiPolynomialValues.FourPeriod
