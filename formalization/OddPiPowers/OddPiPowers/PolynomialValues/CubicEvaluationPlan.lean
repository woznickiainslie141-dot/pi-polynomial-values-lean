module

public import OddPiPowers.PolynomialValues.EvaluationPlan
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AllLabelPairs3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.ZeroOrdinary3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.DirectionMoments3

@[expose] public section

namespace PiPolynomialValues

open FourPeriod PrimeWindow Certificates

theorem cubic_signed_slopes : angleDesign3.fieldTest cubicShape cubicCuts.length=true := by decide +kernel

noncomputable def cubicEvaluationPlan : EvaluationPlan where
  shape := cubicShape
  groups := cubicNodeGroups
  rates := cubicRateData
  design := angleDesign3
  arcs := cubicArcs
  cuts := cubicCuts
  anchor := anchorPlan3
  pad := 229
  degreeA := 141186386926
  degreeB := 44847
  common := 1016064
  margin := 11/100000000
  margin_pos := by decide +kernel
  tests := cubic_rate_tests
  rows := cubic_row_data
  order := cubicScanOrder
  width := List.all_eq_true.mp (by decide +kernel : cubicShape.widths.all (fun w => decide (w≤10000))=true) |>
    fun h w hw => of_decide_eq_true (h w hw)
  nested := cubic_bands_nested
  select := fun t _ hy => cubic_selected t hy
  degree_ratio := by decide +kernel
  square := cubic_scanned_square
  base := cubic_factorial_cost_checked
  primes := cubic_actual_prime_cost
  chain := cubicArcs_chain.1
  checked_arcs := List.all_eq_true.mp cubicArcs_checked
  valid := angleDesign3_valid
  costs := angleDesign3_rates
  moments := angleDesign3_moments
  slopes := cubic_signed_slopes
  cut := by decide +kernel
  mass := cubic_tail_ratios
  zeroRate := ⟨zeroOrdinary3⟩
  references := angleDesign3_references

end PiPolynomialValues
