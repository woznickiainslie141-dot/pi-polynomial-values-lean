module

public import OddPiPowers.PolynomialValues.Numerics.PrimeLocalLedger
public import OddPiPowers.PolynomialValues.Numerics.SlabPrimeRate

/-! Sum the bounds over the complete prime support of the integer
denominator and identify the two certified savings with prime averages. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open PrimeWindow Finset Filter

variable {s : Shape} {g : List (List ℤ)} {K T : ℕ} {cuts : List ℚ} {slabs : List Slab}

theorem PrimeCertificate.sum_local_tail (C : PrimeCertificate s g K T cuts slabs) (t : ℕ) (ht : 0 < t) :
    let N := s.massUnit*t
    (∑ p ∈ Nat.primesLE (primeCeiling s t), localTail s cuts N p*Real.log p) =
      (N : ℝ)^2*(s.totalWidthQ : ℝ)*aggregateTail s cuts N := by
  let N := s.massUnit*t
  let P := Nat.primesLE (primeCeiling s t)
  let f (p u : ℕ) := ((N : ℝ)*(s.totalWidthQ : ℝ)*s.netTailValue (u+1) ((p : ℝ)/N))*Real.log p
  have he := sum_activeLevels cuts s.largestRowQ N P f (fun _ hu _ hp => (C.cut_prime_bounds hu hp).2)
  change (∑ p ∈ P, localTail s cuts N p*Real.log p) = _
  simp only [localTail,sum_mul]
  change (∑ p ∈ P, ∑ u ∈ activeLevels cuts s.largestRowQ N p, f p u) = _
  rw [he]
  change _ = (N : ℝ)^2*(s.totalWidthQ : ℝ)*∑ u ∈ range cuts.length, _
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  unfold f primeAverage
  simp only [mul_assoc,← mul_sum]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_pos C.mass_pos ht).ne'
  dsimp only [N] at hn ⊢
  field_simp [hn] <;> ring

theorem sum_small_cost (s : Shape) (t : ℕ) :
    let S := primeCeiling s t
    (∑ p ∈ Nat.primesLE S, (localSmallCost s t p : ℝ)*Real.log p) ≤
      ((Nat.sqrt S : ℕ) : ℝ)*(layerTotal s t : ℝ)*Real.log S := by
  let S := primeCeiling s t
  let P := (Nat.primesLE S).filter (fun p => p^2 ≤ S)
  have hS : 0 < S := by dsimp [S,primeCeiling]; positivity
  have hh := small_prime_log_sum (J := layerTotal s t) hS P (localSmallCost s t) (by
    intro p hp
    obtain ⟨hm,hp'⟩ := mem_filter.mp hp
    refine ⟨(Nat.mem_primesLE.mp hm).2,by simpa only [pow_two] using hp',?_⟩
    change (if p^2 ≤ S then _ else _) ≤ _
    rw [if_pos hp'])
  calc
    _ = ∑ p ∈ P, (localSmallCost s t p : ℝ)*Real.log p := by
      symm
      apply sum_subset (filter_subset _ _)
      intro p hp hn
      have he : ¬ p^2 ≤ S := fun h => hn (mem_filter.mpr ⟨hp,h⟩)
      simp [localSmallCost,show ¬ p^2 ≤ primeCeiling s t from he]
    _ ≤ _ := hh

theorem PrimeCertificate.global_ledger (C : PrimeCertificate s g K T cuts slabs) :
    ∀ᶠ t : ℕ in atTop, ∀ (a b : ℕ) (y : ℂ) (w : SelectedPolynomial s g t y a b),
      let N := s.massUnit*t
      let S := primeCeiling s t
      Real.log (w.denominator : ℝ) + (N : ℝ)^2*(s.totalWidthQ : ℝ)*aggregateTail s cuts N +
        (N : ℝ)^2*residuePrimeRate s K slabs t ≤
      (primeBaseline s g K t cuts.length : ℝ)*Chebyshev.theta S +
        ((Nat.sqrt S : ℕ) : ℝ)*(layerTotal s t : ℝ)*Real.log S := by
  filter_upwards [C.local_ledger,eventually_gt_atTop (0 : ℕ)] with t hloc ht a b y w
  let N := s.massUnit*t
  let S := primeCeiling s t
  let P := Nat.primesLE S
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.mul_pos C.mass_pos ht
  have hs := sum_le_sum (s := P) (fun p hp => mul_le_mul_of_nonneg_right
    (hloc a b y w p (Nat.mem_primesLE.mp hp).2)
    (show 0 ≤ Real.log (p : ℝ) from Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)))
  simp only [add_mul,sum_add_distrib,← mul_sum] at hs
  have hr : (∑ p ∈ P, (residueReward slabs s K t p : ℝ)*Real.log p) = (N : ℝ)^2*residuePrimeRate s K slabs t := by
    unfold residuePrimeRate
    change _ = (N : ℝ)^2*(_/(N : ℝ)^2)
    field_simp [hn.ne'] <;> rfl
  have hB := log_on_prime_support w.denominator S w.denominator_pos (C.toRowData.prime_support w)
  have htail := C.sum_local_tail t ht
  have hθ := Chebyshev.theta_eq_sum_primesLE_log S
  have hsm := sum_small_cost s t
  change Real.log (w.denominator : ℝ) + (N : ℝ)^2*(s.totalWidthQ : ℝ)*aggregateTail s cuts N +
    (N : ℝ)^2*residuePrimeRate s K slabs t ≤ (primeBaseline s g K t cuts.length : ℝ)*Chebyshev.theta S + _
  rw [hB,← htail,← hr,hθ]
  exact hs.trans (add_le_add le_rfl hsm)

end PiPolynomialValues.FourPeriod
