module

public import OddPiPowers.PolynomialValues.Analysis.TailCapLimit
public import OddPiPowers.PolynomialValues.Analysis.ReflectedColumns

/-! The finite tail estimate has a fixed limit on either face. Both ends
of each band come from the selected determinant's full column enumeration. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter
open scoped Topology

theorem enumerated_tailCap (s : Shape) (hw : ∀ w∈s.widths, w≤10000) {t n V : ℕ}
    (hN : 0 < s.massUnit*t) (m : Fin V → ℕ) (v : Fin V → ℤ) (e : Fin n ≃ Column (s.band t))
    (face : Bool) (k : ℕ) (q : ℝ) :
    tailCap m v (fun i => (bandFrequency s t (columnReflection _ face (e i)) : ℝ)) ((s.massUnit*t : ℕ) : ℝ) k q=
      tailSize m v k/((s.massUnit*t : ℕ) : ℝ)*q+columnExcess s q t := by
  simp only [tailCap,bandFrequency_value s hw hN]
  let A := e.trans (columnReflection _ face)
  have he := A.sum_comp (fun c => twoExcess q ((c.2.val : ℝ)*((s.massUnit*t : ℕ) : ℝ)⁻¹))
  change (tailSize m v k*q+∑ i, twoExcess q (((A i).2.val : ℝ)*((s.massUnit*t : ℕ) : ℝ)⁻¹))/_=_
  rw [he]
  unfold columnExcess
  ring

theorem selected_tailCap_limit {ι : Type*} {F : Filter ι} {t : ι → ℕ} {s : Shape} {g : List (List ℤ)}
    {K a b : ℕ} {y : ι → ℂ} (D : PrimeWindow.RowData s g K) (ht : Tendsto t F atTop)
    (w : ∀ i, SelectedPolynomial s g (t i) (y i) a b) (hw : ∀ x∈s.widths, x≤10000)
    (face : Bool) (c : QuantileCut) (k common : ℕ) (hc : cutTest s common (c,k)=true)
    (hm : tailRatioQ s g k=2*(s.rightMass k : ℚ)/s.massUnit) :
    Tendsto (fun i => tailCap (w i).count (scannedNode g)
      (fun j => (bandFrequency s (t i) (columnReflection _ face ((w i).colIndex j)) : ℝ))
      ((s.massUnit*t i : ℕ) : ℝ) k (c.location s)) F (𝓝 (2*(cutMomentQ s c : ℝ))) := by
  have hq : 0≤c.location s := by unfold QuantileCut.location; positivity
  have H := ((selected_tail_size_limit D ht w k).mul_const (c.location s)).add ((columnExcess_limit s D.mass_pos hq).comp ht)
  have he := actual_quantile_tail s c k common D.mass_pos hc
  rw [hm] at H
  push_cast at H
  have H' : 2*(s.rightMass k : ℝ)/s.massUnit*c.location s+
      2*(∑ j : Fin s.widths.length, ∫ x in -((s.widths.get j : ℝ)/10000)..((s.widths.get j : ℝ)/10000),
          max 0 (x-c.location s))=2*(cutMomentQ s c : ℝ) := by
    unfold cutMomentQ
    push_cast
    linear_combination 2*he
  rw [H'] at H
  apply H.congr'
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℕ))] with i hi
  simpa only [Nat.cast_mul,Function.comp_apply] using
    (enumerated_tailCap s hw (Nat.mul_pos D.mass_pos hi) (w i).count (scannedNode g) (w i).colIndex face k (c.location s)).symm

end PiPolynomialValues.FourPeriod
