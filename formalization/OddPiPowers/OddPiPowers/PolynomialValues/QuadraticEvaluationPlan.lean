module

public import OddPiPowers.PolynomialValues.EvaluationPlan
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AllLabelPairs2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.ZeroOrdinary2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.DirectionMoments2

@[expose] public section

namespace PiPolynomialValues

open FourPeriod PrimeWindow Certificates

theorem quadratic_signed_slopes : angleDesign2.fieldTest quadraticShape quadraticCuts.length=true := by decide +kernel

noncomputable def quadraticEvaluationPlan : EvaluationPlan where
  shape := quadraticShape
  groups := quadraticNodeGroups
  rates := quadraticRateData
  design := angleDesign2
  arcs := quadraticArcs
  cuts := quadraticCuts
  anchor := anchorPlan2
  pad := 73
  degreeA := 27143631494
  degreeB := 4675
  common := 108900
  margin := 8/100000000
  margin_pos := by decide +kernel
  tests := quadratic_rate_tests
  rows := quadratic_row_data
  order := quadraticScanOrder
  width := List.all_eq_true.mp (by decide +kernel : quadraticShape.widths.all (fun w => decide (w≤10000))=true) |>
    fun h w hw => of_decide_eq_true (h w hw)
  nested := quadratic_bands_nested
  select := fun t _ hy => quadratic_selected t hy
  degree_ratio := by decide +kernel
  square := quadratic_scanned_square
  base := quadratic_factorial_cost_checked
  primes := quadratic_actual_prime_cost
  chain := quadraticArcs_chain.1
  checked_arcs := List.all_eq_true.mp quadraticArcs_checked
  valid := angleDesign2_valid
  costs := angleDesign2_rates
  moments := angleDesign2_moments
  slopes := quadratic_signed_slopes
  cut := by decide +kernel
  mass := quadratic_tail_ratios
  zeroRate := ⟨zeroOrdinary2⟩
  references := angleDesign2_references

end PiPolynomialValues
