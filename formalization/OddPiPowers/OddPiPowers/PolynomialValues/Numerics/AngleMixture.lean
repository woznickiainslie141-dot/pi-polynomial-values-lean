module

public import OddPiPowers.PolynomialValues.Numerics.AngularLedger
public import OddPiPowers.PolynomialValues.Numerics.FactorialCostData
public import OddPiPowers.PolynomialValues.Numerics.QuantileCuts

/-! One rational mixture on each angular cell supplies the signed field,
the two reference energy bounds and the off-center charge. Every term
of the angular calculation is a linear form in the actual integrals. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod

structure AngleLabel where
  slopes : List ℤ
  ordinary : ℚ
  tilted : ℚ
  price : ℕ
deriving Inhabited

def AngleLabel.slope (t : AngleLabel) (j : ℕ) : ℚ := ((t.slopes[j]?.getD 0 : ℤ) : ℚ)/100000
def AngleLabel.meanEnergy (t : AngleLabel) : ℚ := (t.ordinary+t.tilted)/2

structure AngleCell where
  arc : ArcRow
  parts : List (ℕ × ℚ)

structure AngleDesign where
  labels : List AngleLabel
  cells : List AngleCell

def AngleDesign.mix (D : AngleDesign) (cell : AngleCell) (f : AngleLabel → ℚ) : ℚ :=
  (cell.parts.map fun p => p.2*f (D.labels[p.1]?.getD default)).sum

def AngleDesign.form (D : AngleDesign) (f : AngleLabel → ℚ) : ArcForm :=
  D.cells.map fun c => (c.arc,D.mix c f)

def AngleDesign.valid (D : AngleDesign) (s : Shape) (arcs : List ArcRow) : Bool := decide
  (D.cells.map AngleCell.arc=arcs ∧
   (D.cells.all fun c => decide ((c.parts.map Prod.snd).sum=1 ∧
      (c.parts.all fun p => decide (p.1<D.labels.length ∧ 0≤p.2))=true))=true ∧
   (D.labels.all fun t => decide (t.slopes.length=s.ratios.length ∧ t.slope 0=0))=true)

def cutMomentQ (s : Shape) (c : QuantileCut) : ℚ :=
  (c.twiceMomentNumerator s : ℚ)/(2*((c.slope : ℚ)*s.massUnit)^2)

def upperNodeMoments (s : Shape) (cuts : List QuantileCut) : List ℚ :=
  let a := cuts.map (cutMomentQ s)
  a.zipWith (· - ·) (a.tail++[0])

def AngleLabel.fieldMoment (t : AngleLabel) (m : List ℚ) : ℚ :=
  (m.zipIdx.map fun p => p.1*t.slope (p.2+1)).sum

def AngleDesign.directionForm (D : AngleDesign) (k : ℕ) := D.form fun t => t.slope (k+1)-t.slope k
def AngleDesign.priceForm (D : AngleDesign) := D.form fun t => (t.price : ℚ)/(2*10^7)
def AngleDesign.energyForm (D : AngleDesign) := D.form AngleLabel.meanEnergy
def AngleDesign.sineForm (D : AngleDesign) (m : List ℚ) (L : ℚ) := D.form fun t => -2*t.fieldMoment m/L

def anglePiLoQ : ℚ := 314159265358979323846/10^20
def anglePiHiQ : ℚ := 314159265358979323847/10^20
def radiusCutQ (d : RateData) : ℚ := (1/d.radius-d.radius)/4

def AngleDesign.checkedRates (D : AngleDesign) (s : Shape) (cuts : List QuantileCut) (d : RateData) : Bool :=
  let m := upperNodeMoments s cuts
  let boundary := anglePiHiQ*radiusCutQ d*d.moment+(D.sineForm m d.length).upper true+D.energyForm.upper false
  decide (0<d.length ∧ 0≤radiusCutQ d ∧ 0≤d.moment ∧ 0≤d.rowSquare ∧
    (List.range cuts.length).all (fun k => decide ((D.directionForm k).upper true<anglePiLoQ*radiusCutQ d))=true ∧
    d.labelPrice≤D.priceForm.lower false ∧
    d.degree*(d.baseCost+d.primeCost)+((d.degree : ℚ)-1)*d.ordinary+
      logTickHi (1/d.radius)*d.rowSquare+boundary≤d.cost)

theorem AngleDesign.form_passes (D : AngleDesign) (s : Shape) (arcs : List ArcRow) (h : D.valid s arcs=true)
    {z : ℚ} (hp : ∀ e∈arcs, e.passes z=true) (f : AngleLabel → ℚ) :
    ∀ p∈D.form f, p.1.passes z=true := by
  have he := (of_decide_eq_true h).1
  intro p hm
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hm
  exact hp c.arc (he ▸ List.mem_map.mpr ⟨c,hc,rfl⟩)

theorem AngleDesign.actual_direction_price (D : AngleDesign) (s : Shape) (cuts : List QuantileCut)
    (d : RateData) (arcs : List ArcRow) (hd : D.valid s arcs=true) (hp : ∀ e∈arcs, e.passes d.radius=true)
    (hr : D.checkedRates s cuts d=true) :
    (∀ k<cuts.length, (D.directionForm k).actual d.radius true < Real.pi*(radiusCutQ d : ℝ)) ∧
      (d.labelPrice : ℝ)≤D.priceForm.actual d.radius false := by
  obtain ⟨_,hc,_,_,hδ,hprice,_⟩ := of_decide_eq_true hr
  have hπ : (anglePiLoQ : ℝ)≤Real.pi := by convert Real.pi_gt_d20.le using 1 <;> norm_num [anglePiLoQ]
  constructor
  · intro k hk
    have hrow := of_decide_eq_true (List.all_eq_true.mp hδ k (List.mem_range.mpr hk))
    have H := ((D.directionForm k).enclose d.radius true (D.form_passes s arcs hd hp _)).2
    have hrow' := (Rat.cast_lt (K := ℝ)).mpr hrow
    rw [Rat.cast_mul] at hrow'
    exact (H.trans_lt hrow').trans_le (mul_le_mul_of_nonneg_right hπ (by exact_mod_cast hc))
  · exact ((Rat.cast_le (K := ℝ)).mpr hprice).trans ((D.priceForm.enclose d.radius false (D.form_passes s arcs hd hp _)).1)

theorem AngleDesign.actual_cost (D : AngleDesign) (s : Shape) (cuts : List QuantileCut)
    (d : RateData) (arcs : List ArcRow) (hd : D.valid s arcs=true) (hp : ∀ e∈arcs, e.passes d.radius=true)
    (hr : D.checkedRates s cuts d=true) (hb : s.basePass d=true) :
    (d.degree : ℝ)*((d.baseCost : ℝ)+d.primeCost)+((d.degree : ℝ)-1)*d.ordinary+
      Real.log (1/(d.radius : ℝ))*d.rowSquare+Real.pi*(radiusCutQ d : ℝ)*d.moment+
      (D.sineForm (upperNodeMoments s cuts) d.length).actual d.radius true+D.energyForm.actual d.radius false≤(d.cost : ℝ) := by
  obtain ⟨_,hc,hm,hs,_,_,hu⟩ := of_decide_eq_true hr
  have hπ : Real.pi≤(anglePiHiQ : ℝ) := by convert Real.pi_lt_d20.le using 1 <;> norm_num [anglePiHiQ]
  have hK := mul_le_mul_of_nonneg_right (s.basePass_sound d hb).2.2 (by exact_mod_cast hs : 0≤(d.rowSquare : ℝ))
  have hA := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hπ
    (by exact_mod_cast hc : 0≤(radiusCutQ d : ℝ))) (by exact_mod_cast hm : 0≤(d.moment : ℝ))
  have hJ := ((D.sineForm (upperNodeMoments s cuts) d.length).enclose d.radius true (D.form_passes s arcs hd hp _)).2
  have hW := (D.energyForm.enclose d.radius false (D.form_passes s arcs hd hp _)).2
  have hU := (Rat.cast_le (K := ℝ)).mpr hu
  push_cast at hU
  linarith only [hK,hA,hJ,hW,hU]

end PiPolynomialValues
