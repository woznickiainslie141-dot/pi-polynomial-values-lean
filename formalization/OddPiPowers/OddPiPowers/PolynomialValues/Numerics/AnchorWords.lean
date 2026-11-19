module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature

/-! Compute each paid word from the full interval minus the spans with
this particular center. The coverage certificate makes the complement
identity exact even at a change of center and at the last grid point. -/

@[expose] public section

namespace PiPolynomialValues

theorem AnchorPlan.ordered {a : AnchorPlan} {l h : ℕ} (hc : a.covers l h=true) : l≤h := by
  induction a generalizing l with
  | nil => exact (of_decide_eq_true hc).le
  | cons p a ih =>
    simp only [covers,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact hc.1.2.le.trans (ih hc.2)

theorem adjacent_word {l m u : ℕ} (hl : l≤m) (hu : m≤u) (d r n : ℕ) :
    ((⟨l,m⟩ : GridSpan).shift d).word spatialBase r n+((⟨m,u⟩ : GridSpan).shift d).word spatialBase r n=
      ((⟨l,u⟩ : GridSpan).shift d).word spatialBase r n := by
  simp only [GridSpan.word_sound (b := spatialBase) _ (by decide : 1<spatialBase),← packedSum_add]
  apply packedSum_congr
  intro i _
  dsimp only [GridSpan.hit,GridSpan.shift]
  split_ifs <;> omega

def AnchorPlan.centerWord (v d r n : ℕ) (a : AnchorPlan) := (a.map fun p =>
  if p.2=v then (p.1.shift d).word spatialBase r n else 0).sum

theorem AnchorPlan.offCenterWord {a : AnchorPlan} {l u : ℕ} (hc : a.covers l u=true) (v d r n : ℕ) (price : ℤ) :
    (a.charges v d price).word spatialBase r n=
    price*(((⟨l,u⟩ : GridSpan).shift d).word spatialBase r n-a.centerWord v d r n) := by
  induction a generalizing l with
  | nil =>
    have he : l=u := of_decide_eq_true hc
    subst u
    simp [charges,centerWord,GridWeights.word,GridSpan.word,GridSpan.shift,spanWord,packedOnes]
  | cons p a ih =>
    simp only [covers,Bool.and_eq_true,decide_eq_true_eq] at hc
    have he := adjacent_word hc.1.2.le (AnchorPlan.ordered hc.2) d r n
    have hspan : (⟨l,p.1.hi⟩ : GridSpan)=p.1 := by rw [← hc.1.1]
    rw [hspan] at he
    change (if p.2=v then 0 else price)*(p.1.shift d).word spatialBase r n+
      (AnchorPlan.charges a v d price).word spatialBase r n=
      price*(((⟨l,u⟩ : GridSpan).shift d).word spatialBase r n-
      ((if p.2=v then (p.1.shift d).word spatialBase r n else 0)+AnchorPlan.centerWord v d r n a))
    rw [ih hc.2,← he]
    split_ifs <;> ring

def anchorStripeCost (rows : List SpatialLane) (a : AnchorPlan) (d : ℕ) (price : ℤ)
    (w : GridWeights) (r : ℕ) (basis : StripeBasis r) :=
  let n := stripeCount r
  let full := ((⟨0,80000⟩ : GridSpan).shift d).word spatialBase r n
  let E (q : SpatialLane × ℕ) := (⟨q.1,[]⟩ : PricedSpatialLane).quickWord r basis+
    price*(full-a.centerWord q.2 d r n)
  packedDot spatialBase spatialBias n (packedMaxList 127 n (10^28) E rows.zipIdx)
    (w.reversedWord spatialBase r n)

theorem anchorStripeCost_eq (rows : List SpatialLane) (a : AnchorPlan) (hc : a.covers 0 80000=true)
    (d : ℕ) (price : ℤ) (w : GridWeights) (r : ℕ) (basis : StripeBasis r) :
    anchorStripeCost rows a d (price*400000000000) w r basis=quickStripeCost (feeLanes rows a d price) w r basis := by
  have he (q : SpatialLane × ℕ) :
      (⟨q.1,a.charges q.2 d (price*400000000000)⟩ : PricedSpatialLane).quickWord r basis=
      (⟨q.1,[]⟩ : PricedSpatialLane).quickWord r basis+(price*400000000000)*
        (((⟨0,80000⟩ : GridSpan).shift d).word spatialBase r (stripeCount r)-a.centerWord q.2 d r (stripeCount r)) := by
    simp only [PricedSpatialLane.quickWord,AnchorPlan.offCenterWord hc]
    simp [GridWeights.word]
  unfold anchorStripeCost quickStripeCost feeLanes packedMaxList
  simp only [List.foldr_map,he]

def anchorReferenceCost (rows : List SpatialLane) (ws : List ℕ) (a : AnchorPlan) (p : ℤ) (r : ℕ) (basis : StripeBasis r) :=
  if p=0 then quickStripeCost (bareLanes rows) (bandWeights ws 0++bandWeights ws 1) r basis
  else quickStripeCost (bareLanes rows) (bandWeights (ws.take 1) 0++bandWeights (ws.take 1) 1) r basis+
    anchorStripeCost rows a 0 (p*400000000000) (bandWeights ws.tail 0) r basis+
    anchorStripeCost rows a 1 (p*400000000000) (bandWeights ws.tail 1) r basis

theorem anchorReferenceCost_eq (rows : List SpatialLane) (ws : List ℕ) (a : AnchorPlan)
    (hc : a.covers 0 80000=true) (p : ℤ) (r : ℕ) (basis : StripeBasis r) :
    anchorReferenceCost rows ws a p r basis=quickReferenceCost rows ws a p r basis := by
  simp only [anchorReferenceCost,quickReferenceCost,anchorStripeCost_eq rows a hc]

end PiPolynomialValues
