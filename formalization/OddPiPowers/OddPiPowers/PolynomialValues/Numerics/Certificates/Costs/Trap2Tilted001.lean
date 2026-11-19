module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted001Block000

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted001Block036. -/
/- Independently checkable declarations from Paid2Tilted001Block036. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488132696310387592240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488132290131250960400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488132005775774316960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131743510768659880000 := by decide +kernel

theorem paid2Tilted001Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1952528735728181529480000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block036Slice036 paid2Tilted001Block036Slice039)) paid2Tilted001Block036Slice042)) paid2Tilted001Block036Slice045))
/- Independently checkable declarations from Paid2Tilted001Block048. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block048Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131533939384823920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block048Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131324224974443800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block048Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131155064583561600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block048Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131009220175651200000 := by decide +kernel

theorem paid2Tilted001Block048 : gridCostBlock 48 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1952525022449118480520000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 48 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block048Slice048 paid2Tilted001Block048Slice051)) paid2Tilted001Block048Slice054)) paid2Tilted001Block048Slice057))
/- Independently checkable declarations from Paid2Tilted001Block060. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block060Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488130880159222896800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block060Slice063 :
    gridCostBlock 63 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488130880159222896800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block060Slice066 :
    gridCostBlock 66 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131009220175651200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block060Slice069 :
    gridCostBlock 69 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131155064583561600000 := by decide +kernel

theorem paid2Tilted001Block060 : gridCostBlock 60 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1952523924603205006400000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 60 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block060Slice060 paid2Tilted001Block060Slice063)) paid2Tilted001Block060Slice066)) paid2Tilted001Block060Slice069))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted001Block072. -/
/- Independently checkable declarations from Paid2Tilted001Block072. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131324224974443800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131533939384823920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488131743510768659880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488132005775774316960000 := by decide +kernel

theorem paid2Tilted001Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1952526607450902244560000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block072Slice072 paid2Tilted001Block072Slice075)) paid2Tilted001Block072Slice078)) paid2Tilted001Block072Slice081))
/- Independently checkable declarations from Paid2Tilted001Block084. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488132290131250960400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488132696310387592240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488133131840422730720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488133526910703175360000 := by decide +kernel

theorem paid2Tilted001Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1952531645192764458720000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block084Slice084 paid2Tilted001Block084Slice087)) paid2Tilted001Block084Slice090)) paid2Tilted001Block084Slice093))
/- Independently checkable declarations from Paid2Tilted001Block096. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block096Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488445024972453227240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block096Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=489136679304752281760000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block096Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488628572711769514880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block096Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488476454027537200720000 := by decide +kernel

theorem paid2Tilted001Block096 : gridCostBlock 96 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1954686731016512224600000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 96 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block096Slice096 paid2Tilted001Block096Slice099)) paid2Tilted001Block096Slice102)) paid2Tilted001Block096Slice105))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted001Block108. -/
/- Independently checkable declarations from Paid2Tilted001Block108. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487752319148932296200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487947444502474481920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487812350442622984320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487677224303280121240000 := by decide +kernel

theorem paid2Tilted001Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1951189338397309883680000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block108Slice108 paid2Tilted001Block108Slice111)) paid2Tilted001Block108Slice114)) paid2Tilted001Block108Slice117))
/- Independently checkable declarations from Paid2Tilted001Block120. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487365976733186889760000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=324880344141795803200000 := by decide +kernel

theorem paid2Tilted001Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=812246320874982692960000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block120Slice120 paid2Tilted001Block120Slice123))
/- Bounded arithmetic from Numerics.Certificates.Costs.Trap2Tilted001. -/
theorem trap2Tilted001 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=20337589434235208609920000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block000 paid2Tilted001Block012)) paid2Tilted001Block024)) paid2Tilted001Block036)) paid2Tilted001Block048)) paid2Tilted001Block060)) paid2Tilted001Block072)) paid2Tilted001Block084)) paid2Tilted001Block096)) paid2Tilted001Block108)) paid2Tilted001Block120))

end PiPolynomialValues.Certificates
