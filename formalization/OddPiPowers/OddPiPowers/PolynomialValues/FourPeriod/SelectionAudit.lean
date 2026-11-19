module

import OddPiPowers.PolynomialValues.FourPeriod.ActualPrefixMinor
import OddPiPowers.PolynomialValues.FourPeriod.OriginOrder

open PiPolynomialValues.FourPeriod

#check (quadratic_actual_prefix_minor : ∀ t : ℕ, ∀ {y : ℂ}, y ≠ 0 →
  ShapeHasPrefixMinor quadraticShape quadraticNodeGroups t y)
#check (cubic_actual_prefix_minor : ∀ t : ℕ, ∀ {y : ℂ}, y ≠ 0 →
  ShapeHasPrefixMinor cubicShape cubicNodeGroups t y)

#print axioms PiPolynomialValues.FourPeriod.quadratic_actual_prefix_minor
#print axioms PiPolynomialValues.FourPeriod.cubic_actual_prefix_minor
#print axioms PiPolynomialValues.FourPeriod.originOrder_dvd_rawDeterminant
