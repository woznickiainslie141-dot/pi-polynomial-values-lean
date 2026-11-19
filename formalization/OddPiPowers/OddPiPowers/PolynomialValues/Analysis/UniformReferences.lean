module

public import OddPiPowers.PolynomialValues.Analysis.SelectedSequence
public import OddPiPowers.PolynomialValues.Analysis.AngularFaceRates

/-! Uniformity over both semicircles and the finite table of angular labels.
The scale and smoothing index are fixed before the maximizing allocation. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Finset Filter Real

namespace EvaluationPlan

noncomputable def ordinaryReference (P : EvaluationPlan) (l : Fin P.design.labels.length) :=
  Classical.choice (P.references (P.design.labels.get l) (List.get_mem _ _)).1

noncomputable def paidReference (P : EvaluationPlan) (l : Fin P.design.labels.length) :=
  Classical.choice (P.references (P.design.labels.get l) (List.get_mem _ _)).2

theorem groups_pos (P : EvaluationPlan) : 0<P.groups.flatten.length := by
  have h := Fintype.card_congr P.order.rank
  simp only [Fintype.card_fin] at h
  rw [h]
  exact List.length_pos_iff.mpr (fun H => by have hp := P.rowSum_pos; simp [H] at hp)

end EvaluationPlan

noncomputable def markedMass {n : ℕ} (h : Fin n → ℕ) (N : ℝ) :=
  N⁻¹*(∑ c, if h c=0 then (0 : ℝ) else 1)

theorem markedMass_nonneg {n : ℕ} (h : Fin n → ℕ) {N : ℝ} (hN : 0≤N) : 0≤markedMass h N := by
  unfold markedMass
  exact mul_nonneg (inv_nonneg.mpr hN) (sum_nonneg (fun _ _ => by split_ifs <;> norm_num))

theorem scaled_mark_price {n : ℕ} (h : Fin n → ℕ) (N fee : ℝ) :
    N⁻¹*(∑ c, if h c=0 then 0 else fee)=markedMass h N*fee := by
  rw [markedMass,mul_assoc,sum_mul]
  congr 1
  exact sum_congr rfl (fun c _ => by split_ifs <;> simp)

namespace SelectedSequence

variable {P : EvaluationPlan} (W : SelectedSequence P)

def referencesFit (k i : ℕ) (ε : ℝ) : Prop :=
  ∀ l : Fin P.design.labels.length,
    W.finiteReference (P.ordinaryReference l) k i≤(P.rates.length : ℝ)*(P.design.labels.get l).ordinary+ε ∧
    W.finiteReference (P.paidReference l) k i≤(P.rates.length : ℝ)*(P.design.labels.get l).tilted+ε

theorem references_fit {ε : ℝ} (hε : 0<ε) : ∀ᶠ k in atTop, ∀ᶠ i in atTop, W.referencesFit k i ε := by
  have H (l : Fin P.design.labels.length) := (W.reference_eventual (P.ordinaryReference l) hε).and
    (W.reference_eventual (P.paidReference l) hε)
  filter_upwards [eventually_all.mpr H] with k hk
  apply eventually_all.mpr
  intro l
  exact ((hk l).1.and (hk l).2).mono (fun _ h => ⟨h.1.le,h.2.le⟩)

theorem block_fit {ε : ℝ} (hε : 0<ε) : ∀ᶠ k in atTop, ∀ᶠ i in atTop,
    (∑ u, blockScaleCost (W.mass i) (innerRadius k) ((W.witness i).count u))≤
      (P.rates.length : ℝ)*P.rates.baseCost+ε := by
  have H := (div_le_iff₀ (mul_pos (by norm_num) P.length_pos)).mp (P.shape.basePass_sound P.rates P.base).1
  have hh : analyticBaseSum P.shape.massList/2≤(P.rates.length : ℝ)*P.rates.baseCost := by
    nlinarith only [H]
  exact (twoStage_upper (fun k => selected_blocks_limit P.rows W.index_atTop W.witness (innerRadius_bounds k).1)
    (scannedBlock_outer P.shape P.groups P.order) hh hε).mono (fun _ H => H.mono (fun _ h => h.le))

end SelectedSequence
end PiPolynomialValues
