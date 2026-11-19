module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.Field2Ordinary086Data
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap2Ordinary086Part000 : gridCostBlock 0 25 (fun r => quickReferenceCost reference2Ordinary086 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-209502035822811342840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary086Part025 : gridCostBlock 25 25 (fun r => quickReferenceCost reference2Ordinary086 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-208020142711697640000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary086Part050 : gridCostBlock 50 25 (fun r => quickReferenceCost reference2Ordinary086 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-208316722067662584640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary086Part075 : gridCostBlock 75 25 (fun r => quickReferenceCost reference2Ordinary086 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-208125311470998199520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary086Part100 : gridCostBlock 100 25 (fun r => quickReferenceCost reference2Ordinary086 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-209266925210269955000000 := by decide +kernel

theorem trap2Ordinary086 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary086 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-1043231137283439722000000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap2Ordinary086Part000 trap2Ordinary086Part025)) trap2Ordinary086Part050)) trap2Ordinary086Part075)) trap2Ordinary086Part100))

end PiPolynomialValues.Certificates
