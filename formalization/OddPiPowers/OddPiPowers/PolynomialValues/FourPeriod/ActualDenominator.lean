module

public import OddPiPowers.PolynomialValues.FourPeriod.ActualDegree
public import OddPiPowers.PolynomialValues.FourPeriod.DenominatorWitness

/-! The same selected prefixes provide a positive common denominator, a
normalized integral polynomial, exact evaluation identity and degree bound. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

def ShapeNormalizedWitness (s : Shape) (groups : List (List ℤ)) (t : ℕ) (y : ℂ)
    (slope error : ℕ) : Prop :=
  ∃ m : Fin groups.flatten.length → ℕ,
    (∀ i, m i ≤ scanRowCount s t (scannedNode groups i)) ∧
    (∑ v, m v) = Fintype.card (Column (s.band t)) ∧
    (∀ i, scanRowCount s t (scannedNode groups i) - m i ≤
      (∑ i, scanRowCount s t (scannedNode groups i)) - Fintype.card (Column (s.band t))) ∧
    ∃ (e : Fin (Fintype.card (Column (s.band t))) ≃ RowCandidates m)
      (d : Fin (Fintype.card (Column (s.band t))) ≃ Column (s.band t)) (B : ℕ) (R : GaussianInt[X]),
      let rows := fun i => (scannedNode groups (e i).1,(e i).2.val)
      let cols := fun j => columnLabel (d j)
      let F := rowFactorial rows
      0 < B ∧ B ∣ F ∧ R.eval₂ GaussianInt.toComplex y ≠ 0 ∧ R.natDegree ≤ slope*t+error ∧
      (∀ x : ℂ, x ^ nodePairOrder (scannedNode groups) m * R.eval₂ GaussianInt.toComplex x =
        (B : ℂ)*normalizedDetValue rows cols x) ∧
      ∀ E : ℕ → ℕ, (∀ p ∈ F.primeFactors,
        C ((p^(F.factorization p-E p) : ℕ) : GaussianInt) ∣ rawDeterminant rows cols) →
        Real.log (B : ℝ) ≤ ∑ p ∈ F.primeFactors, (E p : ℝ)*Real.log p

theorem ShapeDegreeWitness.normalize {s : Shape} {groups : List (List ℤ)} {t slope error : ℕ}
    {y : ℂ} (h : ShapeDegreeWitness s groups t y slope error) :
    ShapeNormalizedWitness s groups t y slope error := by
  obtain ⟨m,hm,hn,hdef,e,d,q,hd,hq,hdeg⟩ := h
  let rows := fun i => (scannedNode groups (e i).1,(e i).2.val)
  let cols := fun j => columnLabel (d j)
  let F := rowFactorial rows
  let B := commonDenominator F q
  obtain ⟨hb,R,_,he,hr,hval⟩ := exists_cleared_quotient rows cols y q hd hq
  refine ⟨m,hm,hn,hdef,e,d,B,R,hb,⟨_,(commonDenominator_split F q).symm⟩,hr,he.le.trans hdeg,hval,?_⟩
  intro E hE
  apply log_commonDenominator_le (rowFactorial_pos rows)
  intro p hp
  apply (C_dvd_strip_origin _ (nodePairOrder (scannedNode groups) m) q).mp
  rw [← hd]
  exact hE p hp

theorem quadratic_actual_normalized (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    ShapeNormalizedWitness quadraticShape quadraticNodeGroups t y 27143631494 4675 :=
  (quadratic_actual_degree t hy).normalize

theorem cubic_actual_normalized (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    ShapeNormalizedWitness cubicShape cubicNodeGroups t y 141186386926 44847 :=
  (cubic_actual_degree t hy).normalize

end PiPolynomialValues.FourPeriod
