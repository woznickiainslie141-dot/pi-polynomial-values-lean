module

public import OddPiPowers.PolynomialValues.SortedConjugates
public import Mathlib.Topology.Sequences

/-! Compactify a finite tuple of normalized root proximities. Truncating
only at the target preserves the lower bound needed for the closest root. -/

@[expose] public section

namespace PiPolynomialValues

open Filter Set Real
open scoped Topology

noncomputable def cappedProximity (C X : ℝ) (ξ z : ℂ) := min C (rootProximity ξ z/max 1 X)

theorem subseq_cappedProximity {k : ℕ} (z : ℕ → Fin k → ℂ) (ξ : ℂ) (X : ℕ → ℝ) {C : ℝ} (hC : 0≤C) :
    ∃ b : Fin k → ℝ, (∀ j, 0≤b j ∧ b j≤C) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, Tendsto (fun i => cappedProximity C (X (φ i)) ξ (z (φ i) j)) atTop (𝓝 (b j)) := by
  let u (i : ℕ) (j : Fin k) : Icc 0 C :=
    ⟨cappedProximity C (X i) ξ (z i j),le_min hC (div_nonneg (rootProximity_nonneg _ _) (le_max_of_le_left zero_le_one)),
      min_le_left _ _⟩
  obtain ⟨b,φ,hφ,H⟩ := CompactSpace.tendsto_subseq u
  refine ⟨fun j => b j,fun j => (b j).2,φ,hφ,fun j => ?_⟩
  exact continuous_subtype_val.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp H) j)

theorem cutoff_principal {X U V C K : ℝ} (hX : 0 < X) (hV : 0≤V) (hK : 0≤K)
    (h : C*X-K≤U+V) : C-V/X-K/X≤min C (U/X) := by
  apply le_min
  · linarith only [div_nonneg hV hX.le,div_nonneg hK hX.le]
  · apply (le_div_iff₀ hX).mpr
    rw [sub_mul,sub_mul,div_mul_cancel₀ _ hX.ne',div_mul_cancel₀ _ hX.ne']
    linarith only [h]

theorem raw_distance_of_proximity {ξ z : ℂ} (hz : ξ≠z) {u : ℝ} (h : u≤rootProximity ξ z) :
    truncatedDistance ξ z≤exp (-u) := by
  rw [← exp_log (positive_truncated_of_ne hz)]
  exact exp_le_exp.mpr (by change u≤ -log (truncatedDistance ξ z) at h; linarith only [h])

theorem distance_of_capped {ξ z : ℂ} (hz : ξ≠z) {C X c : ℝ} (hX : 1≤X)
    (h : c≤cappedProximity C X ξ z) : truncatedDistance ξ z≤exp (-(c*X)) := by
  apply raw_distance_of_proximity hz
  unfold cappedProximity at h
  rw [max_eq_right hX] at h
  exact (le_div_iff₀ (zero_lt_one.trans_le hX)).mp (h.trans (min_le_right _ _))

theorem conjugate_distance_bound {ξ z : ℂ} (hz : ξ≠z) {C X c : ℝ} (hX : 1≤X)
    (hc : c≤cappedProximity C X ξ z) (hm : exp (-(c*X))≤1/2) :
    ‖ξ-z‖≤2*(1+‖ξ‖)*exp (-(c*X)) := by
  have he := distance_of_capped hz hX hc
  exact (rootScale_of_near (he.trans hm)).2.trans (mul_le_mul_of_nonneg_left he (by positivity))

end PiPolynomialValues
