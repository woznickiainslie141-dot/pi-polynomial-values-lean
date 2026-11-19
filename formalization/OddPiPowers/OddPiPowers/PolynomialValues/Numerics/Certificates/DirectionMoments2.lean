module

public import OddPiPowers.PolynomialValues.Analysis.DirectionMoments
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2

@[expose] public section

namespace PiPolynomialValues.Certificates

open FourPeriod

theorem angleDesign2_moments :
    angleDesign2.momentTest quadraticShape quadraticCuts quadraticRateData=true := by decide +kernel

end PiPolynomialValues.Certificates
