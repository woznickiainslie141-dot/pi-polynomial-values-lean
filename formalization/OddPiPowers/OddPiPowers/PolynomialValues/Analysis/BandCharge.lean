module

public import OddPiPowers.PolynomialValues.Analysis.BandIntegral
public import OddPiPowers.PolynomialValues.Analysis.StepCharge
public import OddPiPowers.PolynomialValues.Analysis.AtomicPotential

/-! The total empirical measure of an arbitrary allocation of the actual
columns has a fixed weak limit, including the endpoints of each band. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter
open scoped Topology

noncomputable def bandFrequency (s : Shape) (t : ℕ) (c : Column (s.band t)) : FrequencyInterval :=
  frequencyProjection ((c.2.val : ℝ)*((s.massUnit*t : ℕ) : ℝ)⁻¹)

noncomputable def bandCharge (s : Shape) (t : ℕ) : ContinuousCharge FrequencyInterval :=
  atomicCharge (bandFrequency s t) (fun _ => ((s.massUnit*t : ℕ) : ℝ)⁻¹)

noncomputable def fullBandCharge (s : Shape) : ContinuousCharge FrequencyInterval :=
  ∑ i : Fin s.widths.length, intervalCharge frequencyProjection
    (-((s.widths.get i : ℝ)/10000)) ((s.widths.get i : ℝ)/10000)

theorem bandCharge_limit (s : Shape) (hN : 0<s.massUnit) (f : C(FrequencyInterval,ℝ)) :
    Tendsto (fun t => bandCharge s t f) atTop (𝓝 (fullBandCharge s f)) := by
  simpa only [bandCharge,atomicCharge_apply,← mul_sum,fullBandCharge,ContinuousLinearMap.sum_apply,
    intervalCharge_apply,ContinuousMap.comp_apply,bandFrequency] using
    shape_layer_integral_limit s hN (fun _ => f.comp frequencyProjection)

theorem allocatedCharge_sum {s : Shape} {t V : ℕ} {m : Fin V → ℕ}
    (d : ((v : Fin V) × Fin (m v)) ≃ Column (s.band t)) :
    (∑ v, atomicCharge (fun i => bandFrequency s t (d ⟨v,i⟩))
      (fun _ => ((s.massUnit*t : ℕ) : ℝ)⁻¹)) = bandCharge s t := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.sum_apply,atomicCharge_apply,bandCharge]
  have he := d.sum_comp (fun c => ((s.massUnit*t : ℕ) : ℝ)⁻¹*f (bandFrequency s t c))
  rw [Fintype.sum_sigma] at he
  exact he

theorem bandCharge_residual_limit (s : Shape) (hN : 0<s.massUnit)
    (S : ContinuousCharge FrequencyInterval) (r : ℝ) :
    Tendsto (fun t => (bandCharge s t-fullBandCharge s) (radialPotential unitFrequency r S)) atTop
      (𝓝 0) := by
  simpa only [ContinuousLinearMap.sub_apply,sub_self] using
    (bandCharge_limit s hN (radialPotential unitFrequency r S)).sub_const
      (fullBandCharge s (radialPotential unitFrequency r S))

end PiPolynomialValues.FourPeriod
