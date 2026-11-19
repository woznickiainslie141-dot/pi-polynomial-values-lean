module

public import OddPiPowers.PolynomialValues.FourPeriod.CutRows
public import OddPiPowers.PolynomialValues.FourPeriod.OriginPairs
public import OddPiPowers.PolynomialValues.FourPeriod.ActualPrefixMinor

/-! The same selected integer polynomial can be divided at the origin
and satisfies the degree bounds for every frequency cut simultaneously. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

def HasCutQuotient {κ : Type*} [Fintype κ] {V : ℕ} (count : Fin V → ℕ)
    (node : Fin V → ℤ) (cols : κ → ℤ × ℕ) (w : ℕ) (y : ℂ) : Prop :=
  ∃ m : Fin V → ℕ, (∀ v, m v ≤ count v) ∧ (∑ v, m v) = Fintype.card κ ∧
    (∀ v, count v-m v ≤ (∑ i, count i)-Fintype.card κ) ∧
    ∃ (e : Fin (Fintype.card κ) ≃ RowCandidates m) (d : Fin (Fintype.card κ) ≃ κ)
      (q : GaussianInt[X]),
      rawDeterminant (fun i => (node (e i).1,(e i).2.val)) (fun j => cols (d j)) =
        X ^ nodePairOrder node m * q ∧
      q.eval₂ GaussianInt.toComplex y ≠ 0 ∧
      ∀ z ≤ w, (q.natDegree : ℤ) + (nodePairOrder node m : ℤ) +
        (∑ i, cutQuota w z (e i).2.val) + (∑ j, (bandHit z (cols (d j)).1 : ℤ)) ≤
          ∑ j, ((cols (d j)).2 : ℤ)

theorem HasPrefixMinor.cutQuotient {κ : Type*} [Fintype κ] {V : ℕ} {count : Fin V → ℕ}
    {node : Fin V → ℤ} {cols : κ → ℤ × ℕ} {y : ℂ} (h : HasPrefixMinor count node cols y)
    (w : ℕ) (hw : ∀ j, (cols j).1 ∈ fullBand w) : HasCutQuotient count node cols w y := by
  classical
  obtain ⟨m,hm,hn,hdef,e,d,hval⟩ := h
  let row (i) := (node (e i).1, (e i).2.val)
  let col (j) := cols (d j)
  let P := rawDeterminant row col
  change P.eval₂ GaussianInt.toComplex y ≠ 0 at hval
  have hp : P ≠ 0 := by intro hz; simp [hz] at hval
  obtain ⟨q,hq⟩ := originOrder_dvd_rawDeterminant row col
  have he : originOrder row = nodePairOrder node m := originOrder_prefix_eq node m e
  rw [he] at hq
  change P = X ^ nodePairOrder node m * q at hq
  have hqv : q.eval₂ GaussianInt.toComplex y ≠ 0 := by
    rw [hq,eval₂_mul] at hval
    exact right_ne_zero_of_mul hval
  have hqn : q ≠ 0 := by intro h; simp [h] at hqv
  have hd : P.natDegree = nodePairOrder node m + q.natDegree := by
    rw [hq, natDegree_mul (pow_ne_zero _ X_ne_zero) hqn, natDegree_X_pow]
  refine ⟨m,hm,hn,hdef,e,d,q,hq,hqv,?_⟩
  intro z hz
  have hh := raw_degree_cut e node col w z hz (fun j => hw (d j)) hp
  change (P.natDegree : ℤ) + _ + _ ≤ _ at hh
  rw [hd,Nat.cast_add,add_comm ((nodePairOrder node m : ℕ) : ℤ)] at hh
  exact hh

private theorem shape_band_contains (s : Shape) (t : ℕ) (j : Fin s.widths.length)
    (hj : ∀ i, s.band t i ≤ s.band t j) (c : Column (s.band t)) :
    (columnLabel c).1 ∈ fullBand (s.band t j) :=
  fullBand_mono (hj c.1) c.2.property

theorem quadratic_actual_cut_quotient (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    HasCutQuotient (fun i => scanRowCount quadraticShape t (scannedNode quadraticNodeGroups i))
      (scannedNode quadraticNodeGroups) (columnLabel (U := quadraticShape.band t))
      (quadraticShape.band t ⟨0,by decide⟩) y :=
  (quadratic_actual_prefix_minor t hy).cutQuotient _ (shape_band_contains _ _ _
    (fun i => quadratic_bands_nested t (show 0 ≤ i.val from Nat.zero_le _)))

theorem cubic_actual_cut_quotient (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    HasCutQuotient (fun i => scanRowCount cubicShape t (scannedNode cubicNodeGroups i))
      (scannedNode cubicNodeGroups) (columnLabel (U := cubicShape.band t))
      (cubicShape.band t ⟨0,by decide⟩) y :=
  (cubic_actual_prefix_minor t hy).cutQuotient _ (shape_band_contains _ _ _
    (fun i => cubic_bands_nested t (show 0 ≤ i.val from Nat.zero_le _)))

end PiPolynomialValues.FourPeriod
