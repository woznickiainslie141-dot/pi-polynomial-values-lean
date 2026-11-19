module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceIntegral
public import OddPiPowers.PolynomialValues.Analysis.ReferenceEnergyCost
public import OddPiPowers.PolynomialValues.Numerics.FactorialCostData

/-! Normalize the signed mesh, the two self-interactions and the affine
offsets by the actual length of the signed frequency bands. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Finset

def referenceOffset (s : Shape) (rows : List SpatialLane) : ℚ :=
  ∑ j : Fin rows.length, (s.massList[j.val]?.getD 0)*((rows.get j).β : ℚ)/100000

def spatialRateQ (s : Shape) (rows : List SpatialLane) (trap variation square residual : ℤ) : ℚ :=
  ((trap : ℚ)/(2*40000^2*100000*10^9)+(s.widths.length : ℚ)*variation*22/(4*40000^2*100000)+
    (square : ℚ)/(2*10^12*100000^2)+referenceOffset s rows+
    (min 0 residual : ℤ)/(2*(rows.length : ℚ)*10^12*100000^2))/s.totalWidthQ

noncomputable def continuousReferenceRate (s : Shape) (rows : List SpatialLane) (h : 0 < rows.length)
    (a : AnchorPlan) (p : ℤ) : ℝ :=
  ((∑ i ∈ range 80000, cellValue rows h s.widths a p i)+
    (∑ j : Fin rows.length, (((s.massList[j.val]?.getD 0 : ℚ) : ℝ)*((rows.get j).β : ℝ)/100000-
      laneCharge (rows.get j) (lanePotential (rows.get j))/2))+
    (fullBandCharge s-∑ j : Fin rows.length, laneCharge (rows.get j)) (residualPotential rows s)/(2*rows.length))/
    (s.totalWidthQ : ℝ)

theorem spatial_rate_majorant (basis : (r : ℕ) → StripeBasis r) (E : EnergySection 641 125 0 641)
    (T : EnergySection 80001 1 0 80001) (s : Shape) (rows : List SpatialLane) (hn : 0 < rows.length)
    (hd : ∀ v∈rows, v.passes=true) (hw : s.widths.length≤50) (hb : ∀ w∈s.widths, w≤10000)
    (a : AnchorPlan) (hc : a.covers 0 80000=true) {p : ℤ} (hp : 0≤p)
    (hbudget : (a.length : ℤ)*|p*400000000000|≤10^27)
    (hj : 200000*(s.widths.length : ℤ)+jumpBudget rows≤10^13) :
    continuousReferenceRate s rows hn a p≤(spatialRateQ s rows
      (gridCostBlock 0 125 (fun r => quickReferenceCost rows s.widths a p r (basis r)))
      (referenceVariation rows) (rows.map (regularEnergy E)).sum (residualEnergy T rows s.widths) : ℝ) := by
  have hi := reference_integral_upper basis rows hn hd s.widths hw hb a hc hp hbudget
  have hS := div_le_div_of_nonneg_right (residual_self_cost T s rows hd hb hj)
    (by positivity : 0≤2*(rows.length : ℝ))
  have hQ := sum_le_sum (s := (univ : Finset (Fin rows.length))) (fun j _ =>
    regular_self_cost E (rows.get j) (hd _ (List.get_mem _ _)))
  have hsum : (∑ j : Fin rows.length, (regularEnergy E (rows.get j) : ℝ))=((rows.map (regularEnergy E)).sum : ℝ) := by
    rw [← list_field_sum rows (fun v => (regularEnergy E v : ℝ)),Int.cast_list_sum,List.map_map]
    rfl
  simp only [← sum_div,hsum,sum_neg_distrib,neg_div] at hQ
  unfold continuousReferenceRate spatialRateQ referenceOffset
  simp only [Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast,
    Rat.cast_ofNat,Rat.cast_pow,Rat.cast_sum,Rat.cast_min,Rat.cast_zero,Int.cast_min,Int.cast_zero]
  apply div_le_div_of_nonneg_right _ (by unfold Shape.totalWidthQ; positivity)
  rw [sum_sub_distrib]
  simp only [← sum_div]
  rw [Int.cast_min,Int.cast_zero] at hS
  have hh : (min 0 (residualEnergy T rows s.widths : ℝ))/(10^12*100000^2)/(2*rows.length)=
      min 0 (residualEnergy T rows s.widths : ℝ)/(2*(rows.length : ℝ)*10^12*100000^2) := by ring
  rw [hh] at hS
  linarith only [hi,hQ,hS]

end PiPolynomialValues
