module

public import OddPiPowers.PolynomialValues.Analysis.EndpointFromPlan
public import OddPiPowers.PolynomialValues.QuadraticEvaluationPlan

@[expose] public section

namespace PiPolynomialValues

theorem pi_quadratic_endpoint : Endpoint Real.pi 2 (16161227/1000000) := by
  have h := quadraticEvaluationPlan.endpoint (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change Endpoint Real.pi 2 ((16161227/1000000 : ℚ) : ℝ) at h
  simpa only [Rat.cast_div,Rat.cast_ofNat] using h

theorem pi_quadratic_omega_le : omega Real.pi 2≤((16161227/1000000 : ℝ) : EReal) :=
  pi_quadratic_endpoint.omega_le

end PiPolynomialValues
