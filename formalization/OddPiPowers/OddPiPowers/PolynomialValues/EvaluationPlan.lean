module

public import OddPiPowers.PolynomialValues.Analysis.DesignFields
public import OddPiPowers.PolynomialValues.Analysis.SelectedTailMoments
public import OddPiPowers.PolynomialValues.Analysis.SelectedRowRates
public import OddPiPowers.PolynomialValues.Numerics.ActualPrimeCost
public import OddPiPowers.PolynomialValues.Numerics.ResultantMargin

/-! All finite data used for the evaluations at the conjugate roots.
The coefficients, row floors, analytic prices and selected polynomial
are attached to the same four-period shape. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod PrimeWindow

structure EvaluationPlan where
  shape : Shape
  groups : List (List ℤ)
  rates : RateData
  design : AngleDesign
  arcs : List ArcRow
  cuts : List QuantileCut
  anchor : AnchorPlan
  pad : ℕ
  degreeA : ℕ
  degreeB : ℕ
  common : ℕ
  margin : ℚ
  margin_pos : 0<margin
  tests : rates.passes margin
  rows : RowData shape groups pad
  order : ScanOrder shape groups
  width : ∀ w∈shape.widths, w≤10000
  nested : ∀ t, Antitone (shape.band t)
  select : ∀ (t : ℕ) (y : ℂ), y≠0 → Nonempty (SelectedPolynomial shape groups t y degreeA degreeB)
  degree_ratio : (degreeA : ℚ)/(2*shape.widths.sum*shape.rows.sum)=rates.auxDegree
  square : scannedSquareQ shape groups=2*rates.length*rates.rowSquare
  base : shape.basePass rates=true
  primes : UniformPrimeCost shape groups rates.primeCost
  chain : arcChain 0 1 arcs=true
  checked_arcs : ∀ e∈arcs, e.passes rates.radius=true
  valid : design.valid shape arcs=true
  costs : design.checkedRates shape cuts rates=true
  moments : design.momentTest shape cuts rates=true
  slopes : design.fieldTest shape cuts.length=true
  cut : ∀ k : Fin cuts.length, cutTest shape common (cuts.get k,k.val)=true
  mass : ∀ k : Fin cuts.length, tailRatioQ shape groups k.val=2*(shape.rightMass k.val : ℚ)/shape.massUnit
  zeroRate : Nonempty (ReferenceEvidence shape anchor (List.replicate shape.ratios.length 0) 0 rates.ordinary)
  references : ∀ t∈design.labels, LabelReferencePair shape anchor t

namespace EvaluationPlan

theorem length_pos (P : EvaluationPlan) : 0<(P.rates.length : ℝ) := by exact_mod_cast P.tests.2.2.2.1

theorem degree_scale_pos (P : EvaluationPlan) : 0<(P.rates.scale : ℝ) := by exact_mod_cast P.tests.1

theorem radius_bounds (P : EvaluationPlan) : 0<(P.rates.radius : ℝ) ∧ (P.rates.radius : ℝ)<1 := by
  exact ⟨by exact_mod_cast P.tests.2.1,by exact_mod_cast P.tests.2.2.1⟩

theorem width_eq (P : EvaluationPlan) : P.shape.totalWidthQ=P.rates.length := (of_decide_eq_true P.base).2.1

theorem rowSum_pos (P : EvaluationPlan) : 0<P.shape.rows.sum := by
  by_contra! h
  have he : P.shape.rows.sum=0 := Nat.eq_zero_of_le_zero h
  have hN := P.rows.mass_pos
  simp [Shape.massUnit,he] at hN

theorem direction_margin (P : EvaluationPlan) (k : Fin P.cuts.length) :
    (P.design.directionForm k.val).actual P.rates.radius true<Real.pi/2*radiusMoment P.rates.radius := by
  have h := (P.design.actual_direction_price P.shape P.cuts P.rates P.arcs P.valid P.checked_arcs P.costs).1
    k.val k.isLt
  convert h using 1
  unfold radiusMoment radiusCutQ
  push_cast
  ring

end EvaluationPlan
end PiPolynomialValues
