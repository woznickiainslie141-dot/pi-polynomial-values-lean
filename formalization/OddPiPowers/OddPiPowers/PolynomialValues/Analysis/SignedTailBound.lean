module

public import OddPiPowers.PolynomialValues.Analysis.PhysicalQuantiles
public import OddPiPowers.PolynomialValues.Analysis.AllocationEnergy

/-! Every allocation satisfies the ordered tail estimate on both faces.
Only the row counts and the full set of signed frequencies enter the bound. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

noncomputable def signedIncrement (k : ℕ) (v : ℤ) (d : ℝ) : ℝ :=
  if (k : ℤ) < v then d else if v < -(k : ℤ) then -d else 0

noncomputable def orderedDirection {K : ℕ} (δ : Fin K → ℝ) (v : ℤ) := ∑ k, signedIncrement k.val v (δ k)

def outsideTail (k : ℕ) (v : ℤ) : Bool := decide ((k : ℤ) < v ∨ v < -(k : ℤ))

noncomputable def twoExcess (q x : ℝ) := max 0 (x-q)+max 0 (-x-q)

theorem signed_increment_bound (k : ℕ) (v : ℤ) {δ : ℝ} (hδ : 0≤δ) (q x : ℝ) :
    signedIncrement k v δ*x≤δ*((if outsideTail k v then q else 0)+twoExcess q x) := by
  have h₁ := le_max_right 0 (x-q)
  have h₂ := le_max_right 0 (-x-q)
  have h₃ := le_max_left 0 (x-q)
  have h₄ := le_max_left 0 (-x-q)
  unfold signedIncrement outsideTail twoExcess
  by_cases hp : (k : ℤ) < v
  · simp only [hp,if_true,true_or,decide_true,if_pos rfl]
    apply mul_le_mul_of_nonneg_left _ hδ
    linarith only [h₁,h₄]
  · by_cases hn : v < -(k : ℤ)
    · simp only [hp,hn,if_true,if_false,or_true,decide_true,if_pos rfl,neg_mul,← mul_neg]
      apply mul_le_mul_of_nonneg_left _ hδ
      linarith only [h₂,h₃]
    · simp [hp,hn]
      exact mul_nonneg hδ (add_nonneg h₃ h₄)

noncomputable def tailSize {V : ℕ} (m : Fin V → ℕ) (v : Fin V → ℤ) (k : ℕ) : ℝ :=
  ∑ u, if outsideTail k (v u) then (m u : ℝ) else 0

noncomputable def tailCap {V n : ℕ} (m : Fin V → ℕ) (v : Fin V → ℤ)
    (y : Fin n → ℝ) (N : ℝ) (k : ℕ) (q : ℝ) :=
  (tailSize m v k*q+∑ c, twoExcess q (y c))/N

theorem allocated_tail_direction {V n K : ℕ} (m : Fin V → ℕ)
    (d : ((u : Fin V) × Fin (m u)) ≃ Fin n) (v : Fin V → ℤ) (y : Fin n → ℝ) {N : ℝ} (hN : 0 < N)
    (δ q : Fin K → ℝ) (hδ : ∀ k, 0≤δ k) :
    (∑ u, ∑ i : Fin (m u), orderedDirection δ (v u)*y (d ⟨u,i⟩))/N≤
      ∑ k, δ k*tailCap m v y N k.val (q k) := by
  have ho (Q : ℝ) := d.sum_comp (fun c => twoExcess Q (y c))
  simp only [Fintype.sum_sigma] at ho
  have H (k : Fin K) : (∑ u, ∑ i : Fin (m u), signedIncrement k.val (v u) (δ k)*y (d ⟨u,i⟩))≤
      δ k*(tailSize m v k.val*q k+∑ c, twoExcess (q k) (y c)) := by
    apply (sum_le_sum (fun u _ => sum_le_sum (fun i _ => signed_increment_bound k.val (v u) (hδ k) (q k) (y (d ⟨u,i⟩))))).trans_eq
    simp only [← mul_sum,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,ho,tailSize,sum_mul]
    congr 2
    apply sum_congr rfl
    intro u _
    split_ifs <;> ring
  have he : (∑ u, ∑ i : Fin (m u), orderedDirection δ (v u)*y (d ⟨u,i⟩))=
      ∑ k, ∑ u, ∑ i : Fin (m u), signedIncrement k.val (v u) (δ k)*y (d ⟨u,i⟩) := by
    simp only [orderedDirection,sum_mul]
    calc
      _ = ∑ u, ∑ k, ∑ i : Fin (m u), signedIncrement k.val (v u) (δ k)*y (d ⟨u,i⟩) :=
        sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := sum_comm
  rw [he,sum_div]
  apply sum_le_sum
  intro k _
  exact (div_le_div_of_nonneg_right (H k) hN.le).trans_eq (by unfold tailCap; ring)

theorem twoExcess_reflect (q x : ℝ) : twoExcess q (-x)=twoExcess q x := by simp [twoExcess,add_comm]

end PiPolynomialValues
