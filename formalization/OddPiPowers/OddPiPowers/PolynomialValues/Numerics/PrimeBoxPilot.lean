module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBox

/-! The first nonzero slab from each pinned trapezoid certificate. They
exercise both signs of the collision dual and both strict floor directions. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

def firstQuadraticSlab : Slab :=
  ⟨⟨18000,3481⟩, ⟨60000,11557⟩, [⟨⟨-7405,8⟩, ⟨10000,-10⟩, 1, 1, 3755892090951⟩]⟩

def firstCubicSlab : Slab :=
  ⟨⟨7030260000,490188361⟩, ⟨2750,191⟩, [⟨⟨3820,-10⟩, ⟨0,1⟩, -1, 1, 167585095707⟩]⟩

theorem first_quadratic_slab_checked :
    firstQuadraticSlab.validAfter quadraticShape ⟨5,1⟩ = true ∧ firstQuadraticSlab.credit = 3755892090951 := by
  decide +kernel

theorem first_cubic_slab_checked :
    firstCubicSlab.validAfter cubicShape ⟨8,1⟩ = true ∧ firstCubicSlab.credit = 167585095707 := by
  decide +kernel

end PiPolynomialValues.PrimeWindow
