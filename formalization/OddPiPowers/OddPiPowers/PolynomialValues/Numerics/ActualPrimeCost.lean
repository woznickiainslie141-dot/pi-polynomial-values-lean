module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBaselineRate
import all Mathlib.Data.List.Sort

/-! The complete denominator bound at the exact two certified rational
rates. It holds simultaneously for every nonzero specialization point
and for every selected integral-polynomial witness of the given shape. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open PrimeWindow Filter
open scoped Topology

def primeLimit (s : Shape) (cuts : List ℚ) (slabs : List Slab) : ℚ :=
  (baseCoefficient s : ℚ)/s.massUnit*s.largestRowQ -
    s.totalWidthQ*s.selectedTailIntegral cuts - (((slabs.map Slab.credit).sum : ℕ) : ℚ)/creditScale*s.totalWidthQ

theorem quadratic_prime_limit : primeLimit quadraticShape quadraticTailCuts quadraticSlabs ≤
    quadraticShape.totalWidthQ*quadraticRateData.primeCost := by
  rw [primeLimit,quadraticTail_sum,quadraticSlabs_checked.credit_eq]
  decide +kernel

theorem cubic_prime_limit : primeLimit cubicShape cubicTailCuts cubicSlabs ≤
    cubicShape.totalWidthQ*cubicRateData.primeCost := by
  rw [primeLimit,cubicTail_sum,cubicSlabs_checked.credit_eq]
  decide +kernel

theorem card_ge_width_mass (s : Shape) (t : ℕ) :
    (s.totalWidthQ : ℝ)*((s.massUnit*t : ℕ) : ℝ) ≤ Fintype.card (Column (s.band t)) := by
  rw [shape_column_card]
  simp only [Shape.totalWidthQ,Shape.massUnit,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have h : (0 : ℝ) ≤ s.widths.length := Nat.cast_nonneg _
  linarith only [h]

def UniformPrimeCost (s : Shape) (g : List (List ℤ)) (G : ℚ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, ∀ (a b : ℕ) (y : ℂ) (w : SelectedPolynomial s g t y a b),
    Real.log (w.denominator : ℝ) ≤ ((G : ℝ)+ε)*Fintype.card (Column (s.band t))*((s.massUnit*t : ℕ) : ℝ)

theorem PrimeCertificate.uniform_prime_cost {s : Shape} {g : List (List ℤ)} {K T : ℕ}
    {cuts : List ℚ} {slabs : List Slab} (C : PrimeCertificate s g K T cuts slabs) (G : ℚ) (hG : 0 ≤ G)
    (hcost : primeLimit s cuts slabs ≤ s.totalWidthQ*G) : UniformPrimeCost s g G := by
  intro ε hε
  let W := (s.totalWidthQ : ℝ)
  let z := W*ε/4
  have hw : 0 < W := by
    change (0 : ℝ) < (s.totalWidthQ : ℝ)
    have hh : 0 < s.totalWidthQ := div_pos (mul_pos (by norm_num) (by exact_mod_cast C.widths_pos)) (by norm_num)
    exact_mod_cast hh
  have hz : 0 < z := by dsimp [z]; positivity
  let base := (baseCoefficient s : ℝ)/s.massUnit*(s.largestRowQ : ℝ)
  let tail := W*(s.selectedTailIntegral cuts : ℝ)
  let area := (((slabs.map Slab.credit).sum : ℕ) : ℝ)/creditScale*W
  have hQ : base-tail-area ≤ W*(G : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hcost
    simpa only [primeLimit,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,base,tail,area,W] using hh
  have hbase : ∀ᶠ t : ℕ in atTop, analyticPrimeBaseline s g K cuts.length t < base+z :=
    (C.baseline_rate cuts.length).eventually (gt_mem_nhds (show base < base+z by linarith))
  have htail := ((aggregateTail_tendsto s cuts (fun _ h => C.cut_pos h)).comp
    (massScale_tendsto s C.mass_pos)).const_mul W
  have htlo : ∀ᶠ t : ℕ in atTop, tail-z < W*aggregateTail s cuts (s.massUnit*t) :=
    htail.eventually (lt_mem_nhds (show tail-z < tail by linarith))
  have hone : 1 ≤ (⟨T,1⟩ : Abscissa).value := by
    simpa only [Abscissa.value,Nat.cast_one,div_one] using
      (show (1 : ℝ) ≤ T by exact_mod_cast C.split_pos)
  have harea := all_slabs_prime_rate C.toRowData C.ceiling_ge C.widths_pos slabs ⟨T,1⟩ Nat.zero_lt_one
    hone C.slabs_ok z hz
  filter_upwards [C.normalized_ledger,hbase,htlo,harea,eventually_gt_atTop (0 : ℕ)] with
    t hledger hb ht ha htpos a b y w
  let N := s.massUnit*t
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.mul_pos C.mass_pos htpos
  have h₁ := hledger a b y w
  change Real.log (w.denominator : ℝ)/(N : ℝ)^2+W*aggregateTail s cuts N+residuePrimeRate s K slabs t ≤ _ at h₁
  change area-z ≤ residuePrimeRate s K slabs t at ha
  have hnorm : Real.log (w.denominator : ℝ)/(N : ℝ)^2 ≤ W*((G : ℝ)+ε) := by
    change tail-z < W*aggregateTail s cuts N at ht
    dsimp only [z] at ha hb ht
    linarith only [h₁,ha,hb,ht,hQ,mul_pos hw hε]
  have he := (div_le_iff₀ (sq_pos_of_pos hn)).mp hnorm
  have hg : 0 ≤ (G : ℝ)+ε := add_nonneg (by exact_mod_cast hG) hε.le
  calc
    _ ≤ W*((G : ℝ)+ε)*(N : ℝ)^2 := he
    _ = ((G : ℝ)+ε)*(W*(N : ℝ))*N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (card_ge_width_mass s t) hg) hn.le

theorem quadratic_actual_prime_cost : UniformPrimeCost quadraticShape quadraticNodeGroups quadraticRateData.primeCost :=
  quadratic_prime_certificate.uniform_prime_cost _ (by decide +kernel) quadratic_prime_limit

theorem cubic_actual_prime_cost : UniformPrimeCost cubicShape cubicNodeGroups cubicRateData.primeCost :=
  cubic_prime_certificate.uniform_prime_cost _ (by decide +kernel) cubic_prime_limit

end PiPolynomialValues.FourPeriod
