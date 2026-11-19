module

public import OddPiPowers.PolynomialValues.Analysis.SignedTailBound
public import OddPiPowers.PolynomialValues.Analysis.SelectedScaleLimits
public import OddPiPowers.PolynomialValues.Numerics.AngleMixture

/-! Evaluate the continuum bound for both signed tails at the certified
frequency cut, including every repeated band of the selected shape. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter MeasureTheory
open scoped Topology

theorem twoExcess_integral {w q : ℝ} (hw : 0≤w) (hq : 0≤q) :
    (∫ x in -w..w, twoExcess q x)=2*(∫ x in -w..w, max 0 (x-q)) := by
  let f (x : ℝ) := max 0 (x-q)
  have hf : Continuous f := continuous_const.max (continuous_id.sub continuous_const)
  have h := intervalIntegral.integral_comp_neg (f := f) (a := -w) (b := w)
  change (∫ x in -w..w, f x+f (-x))=_
  have hneg : IntervalIntegrable (fun x => f (-x)) volume (-w) w := (hf.comp continuous_neg).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hf.intervalIntegrable (-w) w) hneg]
  simp only [neg_neg] at h
  rw [h]
  ring

noncomputable def columnExcess (s : Shape) (q : ℝ) (t : ℕ) :=
  ((s.massUnit*t : ℕ) : ℝ)⁻¹*(∑ c : Column (s.band t), twoExcess q ((c.2.val : ℝ)*((s.massUnit*t : ℕ) : ℝ)⁻¹))

theorem columnExcess_limit (s : Shape) (hs : 0 < s.massUnit) {q : ℝ} (hq : 0≤q) :
    Tendsto (columnExcess s q) atTop
      (𝓝 (2*∑ j : Fin s.widths.length, ∫ x in -((s.widths.get j : ℝ)/10000)..((s.widths.get j : ℝ)/10000), max 0 (x-q))) := by
  let f : C(ℝ,ℝ) := ⟨twoExcess q,by unfold twoExcess; fun_prop⟩
  have H := shape_layer_integral_limit s hs (fun _ => f)
  change Tendsto (columnExcess s q) atTop (𝓝 (∑ j : Fin s.widths.length, ∫ x in
    -((s.widths.get j : ℝ)/10000)..((s.widths.get j : ℝ)/10000), twoExcess q x)) at H
  have he (j : Fin s.widths.length) := twoExcess_integral (by positivity : 0≤(s.widths.get j : ℝ)/10000) hq
  simp only [he] at H
  rw [mul_sum]
  exact H

def tailRatioQ (s : Shape) (g : List (List ℤ)) (k : ℕ) : ℚ :=
  ∑ i : Fin g.flatten.length, if outsideTail k (scannedNode g i) then s.rowMassQ (s.ratioAt (scannedNode g i)) else 0

theorem quadratic_tail_ratios : ∀ k : Fin quadraticCuts.length, tailRatioQ quadraticShape quadraticNodeGroups k.val=
    2*(quadraticShape.rightMass k.val : ℚ)/quadraticShape.massUnit := by decide +kernel

theorem cubic_tail_ratios : ∀ k : Fin cubicCuts.length, tailRatioQ cubicShape cubicNodeGroups k.val=
    2*(cubicShape.rightMass k.val : ℚ)/cubicShape.massUnit := by decide +kernel

theorem selected_tail_size_limit {ι : Type*} {F : Filter ι} {t : ι → ℕ} {s : Shape} {g : List (List ℤ)}
    {K a b : ℕ} {y : ι → ℂ} (D : PrimeWindow.RowData s g K) (ht : Tendsto t F atTop)
    (w : ∀ i, SelectedPolynomial s g (t i) (y i) a b) (k : ℕ) :
    Tendsto (fun i => tailSize (w i).count (scannedNode g) k/((s.massUnit*t i : ℕ) : ℝ)) F
      (𝓝 (tailRatioQ s g k : ℝ)) := by
  have H (j : Fin g.flatten.length) : Tendsto (fun i =>
      (if outsideTail k (scannedNode g j) then ((w i).count j : ℝ) else 0)/((s.massUnit*t i : ℕ) : ℝ)) F
      (𝓝 (((if outsideTail k (scannedNode g j) then s.rowMassQ (s.ratioAt (scannedNode g j)) else 0 : ℚ) : ℝ))) := by
    cases he : outsideTail k (scannedNode g j)
    · simpa [he] using (tendsto_const_nhds (f := F) (x := (0 : ℝ)))
    · simpa [he,Shape.rowMassQ,PrimeWindow.rowRate] using selected_mass_limit D ht w j
  simpa only [tailSize,tailRatioQ,Rat.cast_sum,sum_div] using tendsto_finsetSum univ (fun j _ => H j)

end PiPolynomialValues.FourPeriod
