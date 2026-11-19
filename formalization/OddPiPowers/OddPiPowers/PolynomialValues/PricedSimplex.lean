module

public import OddPiPowers.PolynomialValues.Simplex
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The sharp priced simplex inequality for all perturbation labels. -/

@[expose] public section

namespace PiPolynomialValues

def labelPrice (c δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => ((j : ℝ) + 1) * c + δ

def twoLabelMass (t : ℝ) : ℕ → ℝ
  | 0 => 1 - t
  | 1 => t
  | _ + 2 => 0

noncomputable def pricedMinimum (B c δ : ℝ) : ℝ := B - (2 * B - c - δ) ^ 2 / (8 * B)

private theorem sum_twoLabelMass (n : ℕ) (t : ℝ) :
    (∑ j : Fin (n + 2), twoLabelMass t j.val) = 1 := by
  simp [Fin.sum_univ_succ, twoLabelMass]

private theorem twoLabelValue (n : ℕ) (B c δ : ℝ) (hB : 0 < B) :
    let t := (2 * B - c - δ) / (4 * B)
    (∑ j : Fin (n + 2), (labelPrice c δ j.val * twoLabelMass t j.val +
      B * (twoLabelMass t j.val) ^ 2)) = pricedMinimum B c δ := by
  simp [Fin.sum_univ_succ, twoLabelMass, labelPrice, pricedMinimum]
  field_simp [hB.ne']
  ring

theorem priced_simplex_bound {n : ℕ} (B c δ : ℝ) (hB : 0 < B) (hc : 0 ≤ c)
    (hhi : 2 * B ≤ 3 * c + δ)
    (p : Fin (n + 2) → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) :
    pricedMinimum B c δ ≤ ∑ j, (labelPrice c δ j.val * p j + B * p j ^ 2) := by
  let t := (2 * B - c - δ) / (4 * B)
  let q (j : Fin (n + 2)) := twoLabelMass t j.val
  let θ := 2 * B * (1 - t)
  have heq : 4 * B * t = 2 * B - c - δ := by
    dsimp [t]
    field_simp [hB.ne']
  have hqsum : ∑ j, q j = 1 := sum_twoLabelMass n t
  have hlevel (j : Fin (n + 2)) : θ ≤ labelPrice c δ j.val + 2 * B * q j := by
    rcases j with ⟨_ | _ | k, hj⟩
    · simp [θ, labelPrice, q, twoLabelMass]
    · change 2 * B * (1-t) ≤ labelPrice c δ (1 : ℕ) + 2*B*twoLabelMass t 1
      simp only [labelPrice, twoLabelMass, Nat.cast_zero, zero_add, one_mul]
      linarith only [heq]
    · change 2 * B * (1-t) ≤ (((k+1 : ℕ) : ℝ)+1)*c+δ+2*B*0
      push_cast
      nlinarith only [heq, hhi, mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hc]
  have hcontact (j : Fin (n + 2)) : (labelPrice c δ j.val + 2 * B * q j - θ) * q j = 0 := by
    rcases j with ⟨_ | _ | k, hj⟩
    · simp [labelPrice, q, twoLabelMass, θ]
    · apply mul_eq_zero.mpr
      left
      change labelPrice c δ (1 : ℕ) + 2*B*twoLabelMass t 1 - 2*B*(1-t) = 0
      simp only [labelPrice, twoLabelMass, Nat.cast_zero, zero_add, one_mul]
      linarith only [heq]
    · simp [q, twoLabelMass]
  have hval : (∑ j, (labelPrice c δ j.val * q j + B * q j ^ 2)) = pricedMinimum B c δ :=
    twoLabelValue n B c δ hB
  rw [← hval]
  exact simplex_minimum_of_contact _ q p B θ hB.le hp hsum hqsum hlevel hcontact

theorem priced_minimum_attained {n : ℕ} (B c δ : ℝ) (hB : 0 < B) (hc : 0 ≤ c)
    (hδ : 0 ≤ δ) (hlo : c + δ ≤ 2 * B) :
    ∃ p : Fin (n + 2) → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (∑ i, (labelPrice c δ i.val * p i + B * p i ^ 2)) = pricedMinimum B c δ := by
  let t := (2 * B - c - δ) / (4 * B)
  have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
  have ht' : t ≤ 1 := (div_le_one (by linarith : 0 < 4 * B)).mpr (by linarith)
  refine ⟨fun i => twoLabelMass t i.val, ?_, ?_, ?_⟩
  · rintro ⟨_ | _ | k, hk⟩
    · exact sub_nonneg.mpr ht'
    · exact ht
    · exact le_rfl
  · exact sum_twoLabelMass n t
  · exact twoLabelValue n B c δ hB

/-- Uniform control of the loss when secondary roots take total exponent y. -/
theorem priced_minimum_loss {B C δ y Y : ℝ} (hB : 0 < B) (hy : 0 ≤ y) (hY : y ≤ Y) :
    pricedMinimum B C δ - ((2 * B - C + Y - δ) / (4 * B)) * y ≤ pricedMinimum B (C - y) δ := by
  have h : pricedMinimum B (C - y) δ =
      pricedMinimum B C δ - ((2 * B - C + Y - δ) / (4 * B)) * y + y * (2 * Y - y) / (8 * B) := by
    unfold pricedMinimum
    field_simp [hB.ne']
    ring
  rw [h]
  exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hy (by linarith)) (by linarith))

end PiPolynomialValues
