module

public import OddPiPowers.PolynomialValues.Analysis.EndpointFromPlan
public import OddPiPowers.PolynomialValues.CubicEvaluationPlan

@[expose] public section

namespace PiPolynomialValues

theorem pi_cubic_endpoint : Endpoint Real.pi 3 (3426527/125000) := by
  have h := cubicEvaluationPlan.endpoint (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change Endpoint Real.pi 3 ((3426527/125000 : ℚ) : ℝ) at h
  simpa only [Rat.cast_div,Rat.cast_ofNat] using h

theorem pi_cubic_omega_le : omega Real.pi 3≤((3426527/125000 : ℝ) : EReal) :=
  pi_cubic_endpoint.omega_le

end PiPolynomialValues
