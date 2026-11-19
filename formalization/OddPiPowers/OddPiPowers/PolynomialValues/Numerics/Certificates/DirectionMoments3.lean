module

public import OddPiPowers.PolynomialValues.Analysis.DirectionMoments
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign3

@[expose] public section

namespace PiPolynomialValues.Certificates

open FourPeriod

theorem angleDesign3_moments :
    angleDesign3.momentTest cubicShape cubicCuts cubicRateData=true := by decide +kernel

end PiPolynomialValues.Certificates
