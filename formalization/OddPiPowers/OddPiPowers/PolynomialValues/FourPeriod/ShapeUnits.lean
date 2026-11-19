module

public import OddPiPowers.PolynomialValues.FourPeriod.Shape

/-! Common integer units for the balanced bandwidths and row masses. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def Shape.massUnit (s : Shape) : ℕ := 10000 * s.rows.sum

def Shape.rowUnits (s : Shape) (ratio : ℕ) : ℕ := 2 * s.widths.sum * ratio

end PiPolynomialValues.FourPeriod
