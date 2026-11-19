module

public import OddPiPowers.PolynomialValues.Analysis.StepCharge
public import OddPiPowers.PolynomialValues.Analysis.PrimitiveChord

/-! A spatial witness is specified by the jumps of its density.
The potential and the self-interaction are finite sums of the two
spatial primitives at mesh differences. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

noncomputable def tailInterval (x : FrequencyInterval) : SpatialInterval := ⟨x,1,x.2.1,x.2.2,le_rfl⟩

noncomputable def edgeCharge {ι : Type*} [Fintype ι] (x : ι → FrequencyInterval) (d : ι → ℝ) :=
  stepCharge (fun i => tailInterval (x i)) d

theorem energyPrimitive_neg (z : ℝ) : energyPrimitive (-z)=energyPrimitive z := by
  simp [energyPrimitive,Real.log_neg_eq_log]
  <;> ring

theorem edge_potential {ι : Type*} [Fintype ι] (x : ι → FrequencyInterval)
    (d : ι → ℝ) (hd : ∑ i, d i=0) (z : FrequencyInterval) :
    stepPotential (fun i => tailInterval (x i)) d z = ∑ i, d i*logPrimitive ((z : ℝ)-x i) := by
  have he (y : ℝ) : logPrimitive (y-(z : ℝ)) = -logPrimitive ((z : ℝ)-y) := by
    rw [← logPrimitive_neg,neg_sub]
  simp only [stepPotential,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    intervalPotential,ContinuousMap.coe_mk,tailInterval]
  simp_rw [he,neg_sub_neg,mul_sub,sum_sub_distrib,← sum_mul,hd,zero_mul,sub_zero]

theorem edge_interaction {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → FrequencyInterval)
    (y : κ → FrequencyInterval) (d : ι → ℝ) (b : κ → ℝ) (hd : ∑ i, d i=0) (hb : ∑ i, b i=0) :
    edgeCharge x d (stepPotential (fun j => tailInterval (y j)) b) =
      -(∑ i, ∑ j, d i*b j*energyPrimitive ((y j : ℝ)-x i)) := by
  rw [edgeCharge,stepCharge_potential]
  have hj (i : ι) :
      (∑ j, d i*b j*intervalInteraction (tailInterval (x i)) (tailInterval (y j))) =
      -(∑ j, d i*b j*energyPrimitive ((y j : ℝ)-x i))+
        d i*∑ j, b j*energyPrimitive ((y j : ℝ)-1) := by
    have he (j : κ) : d i*b j*intervalInteraction (tailInterval (x i)) (tailInterval (y j)) =
        (d i*energyPrimitive (1-(x i : ℝ)))*b j-d i*b j*energyPrimitive ((y j : ℝ)-x i)+
          d i*(b j*energyPrimitive ((y j : ℝ)-1)) := by
      simp [intervalInteraction,tailInterval,show energyPrimitive 0=0 by simp [energyPrimitive]]
      <;> ring
    simp only [he,sum_add_distrib,sum_sub_distrib,← mul_sum,hb,mul_zero,zero_sub]
  simp only [hj,sum_add_distrib,sum_neg_distrib,← sum_mul,hd,zero_mul,add_zero]

theorem interval_as_tails (a b : FrequencyInterval) :
    intervalCharge frequencyProjection a b =
      intervalCharge frequencyProjection a 1-intervalCharge frequencyProjection b 1 := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.sub_apply,intervalCharge_apply]
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    ((f.continuous.comp frequencyProjection.continuous).intervalIntegrable (a : ℝ) (b : ℝ))
    ((f.continuous.comp frequencyProjection.continuous).intervalIntegrable (b : ℝ) 1)
  exact eq_sub_of_add_eq h

end PiPolynomialValues
