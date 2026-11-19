module

public import OddPiPowers.PolynomialValues.Numerics.SpatialLane
public import OddPiPowers.PolynomialValues.Numerics.PackedMaximum
public import OddPiPowers.PolynomialValues.Numerics.PackedDot
public import OddPiPowers.PolynomialValues.Numerics.PackedIntervals
public import OddPiPowers.PolynomialValues.Analysis.PricedBandCells

/-! A signed linear combination of grid intervals supplies the exact
quadrature weights and the surcharge for each node. Each stripe checks
the maximum over all nodes, and its scalar product with the weights. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

abbrev GridWeights := List (GridSpan × ℤ)

def GridWeights.val (s : GridWeights) (i : ℕ) := (s.map fun p => p.2*p.1.hit i).sum

def GridWeights.word (s : GridWeights) (b : ℤ) (r n : ℕ) := (s.map fun p => p.2*p.1.word b r n).sum
def GridWeights.reversedWord (s : GridWeights) (b : ℤ) (r n : ℕ) := (s.map fun p => p.2*p.1.reversedWord b r n).sum

theorem GridWeights.word_sound (s : GridWeights) {b : ℤ} (hb : 1<b) (r n : ℕ) :
    s.word b r n=packedSum b n (fun k => s.val (r+125*k)) := by
  induction s with
  | nil => simp [word,val,packedSum]
  | cons p s ih =>
    change p.2*p.1.word b r n+GridWeights.word s b r n=_
    rw [p.1.word_sound hb,ih,← packedSum_scale,← packedSum_add]
    rfl

theorem GridWeights.reversedWord_sound (s : GridWeights) {b : ℤ} (hb : 1<b) (r n : ℕ) :
    s.reversedWord b r n=packEval b n (fun j => s.val (r+125*(n-1-j))) := by
  induction s with
  | nil => simp [reversedWord,val,packEval_eq,packedSum]
  | cons p s ih =>
    change p.2*p.1.reversedWord b r n+GridWeights.reversedWord s b r n=_
    rw [p.1.reversedWord_sound hb,ih,packEval_eq,packEval_eq,packEval_eq,← packedSum_scale,← packedSum_add]
    rfl

structure PricedSpatialLane where
  lane : SpatialLane
  surcharge : GridWeights

def PricedSpatialLane.sample (p : PricedSpatialLane) (r k : ℕ) :=
  p.lane.sample r k+p.surcharge.val (r+125*k)

def PricedSpatialLane.word (p : PricedSpatialLane) (r : ℕ) (basis : StripeBasis r) :=
  p.lane.word r basis+p.surcharge.word spatialBase r (stripeCount r)

theorem PricedSpatialLane.word_sound {p : PricedSpatialLane} (hp : p.lane.passes=true) {r : ℕ} (hr : r<125)
    (basis : StripeBasis r) : p.word r basis=packedSum spatialBase (stripeCount r) (p.sample r) := by
  rw [word,p.lane.word_sound hp hr,p.surcharge.word_sound (by decide : 1<spatialBase),← packedSum_add]
  rfl

def stripeEnvelope (rows : List PricedSpatialLane) (r : ℕ) (basis : StripeBasis r) :=
  packedMaxList 127 (stripeCount r) (10^28) (fun p => p.word r basis) rows

def stripeEnvelopeValue (rows : List PricedSpatialLane) (r k : ℕ) :=
  maxWithFloor (-(10^28)) (fun p => p.sample r k) rows

theorem stripeEnvelope_sound (rows : List PricedSpatialLane) {r : ℕ} (hr : r<125) (basis : StripeBasis r)
    (h₁ : ∀ p∈rows, p.lane.passes=true)
    (h₂ : ∀ p∈rows, ∀ k<stripeCount r, |p.surcharge.val (r+125*k)|≤10^27) :
    stripeEnvelope rows r basis=packedSum spatialBase (stripeCount r) (stripeEnvelopeValue rows r) ∧
      ∀ k<stripeCount r, |stripeEnvelopeValue rows r k|≤10^28 := by
  have h (p : PricedSpatialLane) (hp : p∈rows) (k : ℕ) (hk : k<stripeCount r) : |p.sample r k|≤10^28 := by
    have ha := abs_le.mp (p.lane.sample_range (h₁ p hp) hr hk)
    have hb := abs_le.mp (h₂ p hp k hk)
    unfold PricedSpatialLane.sample
    rw [abs_le]
    constructor <;> omega
  exact ⟨packedMaxList_sound _ _ (by decide) (by decide) _ _ _ (fun p hp => p.word_sound (h₁ p hp) hr basis) h,
    fun k hk => maxWithFloor_range (by decide) _ _ (fun p hp => h p hp k hk)⟩

def stripeWeightedCost (rows : List PricedSpatialLane) (w : GridWeights) (r : ℕ) (basis : StripeBasis r) :=
  packedDot spatialBase spatialBias (stripeCount r) (stripeEnvelope rows r basis)
    (w.reversedWord spatialBase r (stripeCount r))

theorem stripeWeightedCost_sound (rows : List PricedSpatialLane) (w : GridWeights) {r : ℕ} (hr : r<125)
    (basis : StripeBasis r) (h₁ : ∀ p∈rows, p.lane.passes=true)
    (h₂ : ∀ p∈rows, ∀ k<stripeCount r, |p.surcharge.val (r+125*k)|≤10^27)
    (hw : ∀ k<stripeCount r, |w.val (r+125*k)|≤100) :
    stripeWeightedCost rows w r basis=∑ k ∈ range (stripeCount r), w.val (r+125*k)*stripeEnvelopeValue rows r k := by
  obtain ⟨he,hh⟩ := stripeEnvelope_sound rows hr basis h₁ h₂
  have hn : 0<stripeCount r := by unfold stripeCount; split <;> decide
  have hs : (∑ k ∈ range (stripeCount r), |stripeEnvelopeValue rows r k|)≤641*10^28 := by
    apply (sum_le_sum (fun k hk => hh k (mem_range.mp hk))).trans
    simp only [sum_const,card_range,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by decide)
    unfold stripeCount
    split <;> decide
  rw [stripeWeightedCost,he,w.reversedWord_sound (by decide : 1<spatialBase)]
  exact packedDot_sound (by decide) hn (stripeEnvelopeValue rows r) (fun k => w.val (r+125*k))
    (by decide) hw hs (by decide) (by decide)

theorem sum_full_stripes {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    (∑ r ∈ range 125, ∑ k ∈ range (stripeCount r), f (r+125*k))=∑ i ∈ range 80001, f i := by
  have he (r : ℕ) : (∑ k ∈ range (stripeCount r), f (r+125*k))=
      (∑ k ∈ range 640, f (r+125*k))+(if r=0 then f 80000 else 0) := by
    by_cases h : r=0
    · subst r
      rw [show stripeCount 0=640+1 by decide,sum_range_succ]
      simp
    · simp [stripeCount,h]
  simp only [he,sum_add_distrib]
  rw [sum_ite_eq' (range 125),if_pos (by decide),sum_range_succ (n := 80000)]
  apply congrArg (fun z : A => z+f 80000)
  rw [show (80000 : ℕ)=640*125 by decide,FourPeriod.sum_grid_blocks f 640 125,sum_comm]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro k _
  congr 1
  omega

end PiPolynomialValues
