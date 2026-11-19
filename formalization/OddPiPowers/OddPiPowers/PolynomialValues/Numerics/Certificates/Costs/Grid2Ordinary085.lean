module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.Field2Ordinary085Data
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap2Ordinary085Part000 : gridCostBlock 0 25 (fun r => quickReferenceCost reference2Ordinary085 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-537359080928200480720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary085Part025 : gridCostBlock 25 25 (fun r => quickReferenceCost reference2Ordinary085 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-536032902806194296120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary085Part050 : gridCostBlock 50 25 (fun r => quickReferenceCost reference2Ordinary085 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-536258031205864796240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary085Part075 : gridCostBlock 75 25 (fun r => quickReferenceCost reference2Ordinary085 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-536113124462332891000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary085Part100 : gridCostBlock 100 25 (fun r => quickReferenceCost reference2Ordinary085 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-537164436497967178400000 := by decide +kernel

theorem trap2Ordinary085 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary085 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-2682927575900559642480000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap2Ordinary085Part000 trap2Ordinary085Part025)) trap2Ordinary085Part050)) trap2Ordinary085Part075)) trap2Ordinary085Part100))

end PiPolynomialValues.Certificates
