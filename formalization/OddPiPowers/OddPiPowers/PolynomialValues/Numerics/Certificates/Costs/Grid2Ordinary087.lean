module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.Field2Ordinary087Data
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap2Ordinary087Part000 : gridCostBlock 0 25 (fun r => quickReferenceCost reference2Ordinary087 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-6786575802837519960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary087Part025 : gridCostBlock 25 25 (fun r => quickReferenceCost reference2Ordinary087 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-5215925855368414960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary087Part050 : gridCostBlock 50 25 (fun r => quickReferenceCost reference2Ordinary087 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-5554025790884950480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary087Part075 : gridCostBlock 75 25 (fun r => quickReferenceCost reference2Ordinary087 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-5335645831585443840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap2Ordinary087Part100 : gridCostBlock 100 25 (fun r => quickReferenceCost reference2Ordinary087 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-6528136955146070360000 := by decide +kernel

theorem trap2Ordinary087 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary087 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-29420310235822399600000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap2Ordinary087Part000 trap2Ordinary087Part025)) trap2Ordinary087Part050)) trap2Ordinary087Part075)) trap2Ordinary087Part100))

end PiPolynomialValues.Certificates
