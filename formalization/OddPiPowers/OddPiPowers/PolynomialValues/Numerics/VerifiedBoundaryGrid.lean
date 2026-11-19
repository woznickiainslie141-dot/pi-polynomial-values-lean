module

public import OddPiPowers.PolynomialValues.Numerics.WeightedEnvelope
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.Reference2Ordinary000

/-! Specialize the full-grid and sample bounds to the stored integer
certificates. The first complete reference has all seven signed nodes. -/

@[expose] public section

namespace PiPolynomialValues.Certificates

open Finset

theorem certified_stripe_cost (rows : List PricedSpatialLane) (w : GridWeights) {r : ℕ} (hr : r<125)
    (h₁ : ∀ p∈rows, p.lane.passes=true)
    (h₂ : ∀ p∈rows, ∀ k<stripeCount r, |p.surcharge.val (r+125*k)|≤10^27)
    (hw : ∀ k<stripeCount r, |w.val (r+125*k)|≤100) :
    stripeWeightedCost rows w r (spatialBasis r)=
      ∑ k ∈ range (stripeCount r), w.val (r+125*k)*stripeEnvelopeValue rows r k :=
  stripeWeightedCost_sound rows w hr (spatialBasis r) h₁ h₂ hw

theorem quadratic_zero_field_samples (v : SpatialLane) (hv : v∈reference2Ordinary000)
    {r k : ℕ} (hr : r<125) (hk : k<stripeCount r) :
    v.realField (((r : ℝ)+125*k)/40000-1)≤(v.sample r k : ℝ)/(40000*100000*10^9) :=
  v.sample_upper (List.all_eq_true.mp reference2Ordinary000_checked v hv) hr hk

end PiPolynomialValues.Certificates
