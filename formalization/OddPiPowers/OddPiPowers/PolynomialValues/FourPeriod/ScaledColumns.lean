module

public import OddPiPowers.PolynomialValues.FourPeriod.CutRows
public import OddPiPowers.PolynomialValues.FourPeriod.Columns

/-! Exact total length, derivative-layer moment, and number of central
frequencies when every integer half-bandwidth is multiplied by a scale. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

def scaledLength {J : ℕ} (u : Fin J → ℕ) : ℕ := ∑ j, 2 * u j
def scaledLayer {J : ℕ} (u : Fin J → ℕ) : ℕ := ∑ j, 2 * u j * j.val
def scaledHits {J : ℕ} (u : Fin J → ℕ) (z : ℕ) : ℕ := ∑ j, 2 * min z (u j)
def layerConstant (J : ℕ) : ℕ := ∑ j : Fin J, j.val

theorem min_times_scale (a b t : ℕ) : min (a*t) (b*t) = min a b * t := by
  rcases le_total a b with h|h
  · rw [min_eq_left h, min_eq_left (Nat.mul_le_mul_right t h)]
  · rw [min_eq_right h, min_eq_right (Nat.mul_le_mul_right t h)]

theorem column_card_scaled {J : ℕ} (u : Fin J → ℕ) (t : ℕ) :
    Fintype.card (Column (fun j => u j * t)) = scaledLength u * t + J := by
  rw [column_card, sum_add_distrib]
  simp only [scaledLength, sum_mul, Nat.mul_assoc, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_id]

theorem column_layer_scaled {J : ℕ} (u : Fin J → ℕ) (t : ℕ) :
    (∑ c : Column (fun j => u j * t), (columnLabel c).2) = scaledLayer u * t + layerConstant J := by
  rw [Fintype.sum_sigma]
  unfold scaledLayer layerConstant
  rw [sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  change (∑ _ : ↥(fullBand (u j * t)), j.val) = _
  rw [sum_const,card_univ,Fintype.card_coe,card_fullBand,nsmul_eq_mul]
  unfold bandSize
  change (2*(u j*t)+1)*j.val = (2*u j*j.val)*t + j.val
  ring

private theorem band_hits_sum (w z : ℕ) :
    (∑ c : ↥(fullBand w), bandHit z c.val) = bandSize (min z w) := by
  rw [Finset.sum_coe_sort]
  unfold bandHit
  rw [Finset.sum_boole]
  have hs : (fullBand w).filter (fun k => k ∈ fullBand z) = fullBand (min z w) := by
    apply Finset.ext
    intro k
    rw [mem_filter]
    rcases le_total z w with h|h
    · rw [min_eq_left h]
      exact ⟨And.right,fun h' => ⟨fullBand_mono h h',h'⟩⟩
    · rw [min_eq_right h]
      exact ⟨And.left,fun h' => ⟨h',fullBand_mono h h'⟩⟩
  rw [hs,card_fullBand]
  rfl

theorem column_hits_scaled {J : ℕ} (u : Fin J → ℕ) (t z : ℕ) :
    (∑ c : Column (fun j => u j * t), bandHit (z*t) (columnLabel c).1) = scaledHits u z*t+J := by
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ j, (2 * min z (u j) * t + 1) := by
      apply sum_congr rfl
      intro j _
      change (∑ c : ↥(fullBand (u j*t)), bandHit (z*t) c.val) = _
      rw [band_hits_sum,min_times_scale,bandSize,Nat.mul_assoc]
    _ = _ := by
      rw [sum_add_distrib, scaledHits, sum_mul]
      simp

end PiPolynomialValues.FourPeriod
