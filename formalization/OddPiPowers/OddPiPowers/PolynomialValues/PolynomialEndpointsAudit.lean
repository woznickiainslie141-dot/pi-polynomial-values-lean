module

import OddPiPowers.PolynomialValues.PolynomialEndpoints

open PiPolynomialValues

example : Endpoint Real.pi 2 (16161227/1000000) := pi_quadratic_endpoint
example : Endpoint Real.pi 3 (3426527/125000) := pi_cubic_endpoint
example : omega Real.pi 2≤((16161227/1000000 : ℝ) : EReal) := pi_quadratic_omega_le
example : omega Real.pi 3≤((3426527/125000 : ℝ) : EReal) := pi_cubic_omega_le

#print axioms PiPolynomialValues.pi_quadratic_endpoint
#print axioms PiPolynomialValues.pi_cubic_endpoint
#print axioms PiPolynomialValues.pi_quadratic_omega_le
#print axioms PiPolynomialValues.pi_cubic_omega_le
