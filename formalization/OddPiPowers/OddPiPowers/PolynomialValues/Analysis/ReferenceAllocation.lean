module

public import OddPiPowers.PolynomialValues.Analysis.ReferenceEnergyCost
public import OddPiPowers.PolynomialValues.Analysis.AllocatedBlockRate

/-! Compare an arbitrary allocation directly with a checked reference.
The interpolation error of the radial potential is uniform in the allocated
columns. A price paid by a positive Taylor label is subtracted columnwise. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Filter
open scoped Topology

noncomputable def referenceRadialError (rows : List SpatialLane) (r : ℝ) :=
  ∑ i : Fin rows.length, ‖radialPotential unitFrequency r (laneCharge (rows.get i))-lanePotential (rows.get i)‖

theorem referenceRadialError_limit (rows : List SpatialLane) :
    Tendsto (fun k => referenceRadialError rows (innerRadius k)) atTop (𝓝 0) := by
  have H (j : Fin rows.length) : Tendsto (fun k => radialPotential unitFrequency (innerRadius k) (laneCharge (rows.get j)))
      atTop (𝓝 (lanePotential (rows.get j))) :=
    meshReference_radial_limit (n := 641) (step := 125) (by decide) (rows.get j).jump
      (fun k => (innerRadius_bounds k).1) (fun k => (innerRadius_bounds k).2) innerRadius_tendsto
  have H' (j : Fin rows.length) : Tendsto (fun k => ‖radialPotential unitFrequency (innerRadius k) (laneCharge (rows.get j))-
      lanePotential (rows.get j)‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp (H j)
  simpa only [referenceRadialError,sum_const_zero] using tendsto_finsetSum univ (fun j _ => H' j)

attribute [local irreducible] radialPotential lanePotential laneCharge meshReference meshLimitPotential

theorem reference_allocation_bound {n V : ℕ} (m : Fin V → ℕ) (hV : 0 < V)
    (d : ((v : Fin V) × Fin (m v)) ≃ Fin n) (y : Fin n → FrequencyInterval) {N r : ℝ}
    (hN : 0 < N) (hr : 0≤r) (hr1 : r < 1) (rows : List SpatialLane) (hd : ∀ v∈rows, v.passes=true)
    (rank : Fin V ≃ Fin rows.length) (s : FourPeriod.Shape) (hw : ∀ w∈s.widths, w≤10000)
    (g fee : Fin n → ℝ)
    (hg : ∀ v i, (rows.get (rank v)).realField (y (d ⟨v,i⟩) : ℝ)+fee (d ⟨v,i⟩)≤g (d ⟨v,i⟩)) :
    let P := allocationCharge m d y N
    let Q (v : Fin V) := laneCharge (rows.get (rank v))
    let S := meshReference (n := 80001) (step := 1) (by decide) (residualJump rows s.widths)
    (∑ v, (P v (FourPeriod.linearFrequency (((rows.get (rank v)).slope : ℝ)/100000))+
       radialInteraction unitFrequency r (P v) (P v)/2)) ≤
      N⁻¹*((∑ c, g c)-(∑ c, fee c)+(n : ℝ)*referenceRadialError rows r)+
      (∑ v, ((m v : ℝ)/N*(((rows.get (rank v)).β : ℝ)/100000)-radialInteraction unitFrequency r (Q v) (Q v)/2))+
      (2*((∑ v, P v)-FourPeriod.fullBandCharge s) (radialPotential unitFrequency r S)+
        radialInteraction unitFrequency r S S)/(2*V) := by
  intro P Q S
  let f (v : Fin V) := FourPeriod.linearFrequency (((rows.get (rank v)).slope : ℝ)/100000)
  let β (v : Fin V) := ((rows.get (rank v)).β : ℝ)/100000
  let p (c : Fin n) := g c-fee c+referenceRadialError rows r
  have hc (v : Fin V) (i : Fin (m v)) :
      f v (y (d ⟨v,i⟩))+radialPotential unitFrequency r (Q v) (y (d ⟨v,i⟩))≤p (d ⟨v,i⟩)+β v := by
    let a := rows.get (rank v)
    let z := y (d ⟨v,i⟩)
    let U := radialPotential unitFrequency r (laneCharge (rows.get (rank v)))-lanePotential (rows.get (rank v))
    have hU := (ContinuousMap.norm_coe_le_norm U z)
    have hsum : ‖U‖≤referenceRadialError rows r :=
      single_le_sum (s := univ) (f := fun i : Fin rows.length => ‖radialPotential unitFrequency r
        (laneCharge (rows.get i))-lanePotential (rows.get i)‖) (fun _ _ => norm_nonneg _) (mem_univ (rank v))
    have he := lane_real_potential a (hd _ (List.get_mem _ _)) z
    have hpoint : radialPotential unitFrequency r (Q v) z-lanePotential a z≤referenceRadialError rows r :=
      (le_abs_self _).trans (hU.trans hsum)
    change (a.slope : ℝ)/100000*(z : ℝ)+radialPotential unitFrequency r (Q v) z≤
      g (d ⟨v,i⟩)-fee (d ⟨v,i⟩)+referenceRadialError rows r+(a.β : ℝ)/100000
    have he' : a.realField z=(a.slope : ℝ)/100000*(z : ℝ)+lanePotential a z-(a.β : ℝ)/100000 := by
      simpa only [lanePotential] using he
    have hh : a.realField z+fee (d ⟨v,i⟩)≤g (d ⟨v,i⟩) := hg v i
    linarith only [hh,hpoint,he']
  have H := allocation_energy_bound m hV d y hN unitFrequency unitFrequency_norm hr hr1 Q
    (FourPeriod.fullBandCharge s) f β p hc
  have he : FourPeriod.fullBandCharge s-∑ v, Q v=S := by
    rw [show (∑ v, Q v)=∑ j : Fin rows.length, laneCharge (rows.get j) from
      rank.sum_comp (fun j => laneCharge (rows.get j))]
    simpa only [laneCharge,S] using (residual_meshReference s rows hw).symm
  dsimp only at H
  rw [he] at H
  simpa only [p,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using H

end PiPolynomialValues
