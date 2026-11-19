module

public import OddPiPowers.PolynomialValues.FourPeriod.ActualDenominator
public import OddPiPowers.PolynomialValues.FourPeriod.SmallPrimeBound
public import OddPiPowers.PolynomialValues.FourPeriod.PrimeCutDenominator
public import OddPiPowers.PolynomialValues.FourPeriod.ResidueDenominator

/-! All prime estimates, the analytic evaluation identity, and the degree
bound refer to the same selected polynomial at the prescribed point. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

structure SelectedPolynomial (s : Shape) (g : List (List ℤ)) (t : ℕ) (y : ℂ) (a b : ℕ) where
  count : Fin g.flatten.length → ℕ
  cap : ∀ v, count v ≤ scanRowCount s t (scannedNode g v)
  total : ∑ v, count v = Fintype.card (Column (s.band t))
  deficit : ∀ v, scanRowCount s t (scannedNode g v) - count v ≤
    (∑ i, scanRowCount s t (scannedNode g i)) - Fintype.card (Column (s.band t))
  rowIndex : Fin (Fintype.card (Column (s.band t))) ≃ RowCandidates count
  colIndex : Fin (Fintype.card (Column (s.band t))) ≃ Column (s.band t)
  quotient : GaussianInt[X]
  quotient_eval_ne : quotient.eval₂ GaussianInt.toComplex y ≠ 0
  raw_eq : rawDeterminant (fun i => (scannedNode g (rowIndex i).1,(rowIndex i).2.val))
    (fun j => columnLabel (colIndex j)) = X^(nodePairOrder (scannedNode g) count)*quotient
  integral : GaussianInt[X]
  eval_ne : integral.eval₂ GaussianInt.toComplex y ≠ 0
  degree_le : integral.natDegree ≤ a*t+b
  identity : ∀ x : ℂ, x^(nodePairOrder (scannedNode g) count)*integral.eval₂ GaussianInt.toComplex x =
    ((commonDenominator (rowFactorial (fun i => (scannedNode g (rowIndex i).1,(rowIndex i).2.val))) quotient : ℕ) : ℂ)*
    normalizedDetValue (fun i => (scannedNode g (rowIndex i).1,(rowIndex i).2.val)) (fun j => columnLabel (colIndex j)) x

variable {s : Shape} {g : List (List ℤ)} {t a b : ℕ} {y : ℂ}

theorem ShapeDegreeWitness.selected (hw : ShapeDegreeWitness s g t y a b) :
    Nonempty (SelectedPolynomial s g t y a b) := by
  obtain ⟨m,hm,hn,hdef,e,d,q,hd,hq,hdeg⟩ := hw
  obtain ⟨_,R,_,he,hr,hi⟩ := exists_cleared_quotient _ _ y q hd hq
  exact ⟨⟨m,hm,hn,hdef,e,d,q,hq,hd,R,hr,he.le.trans hdeg,hi⟩⟩

theorem quadratic_selected (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    Nonempty (SelectedPolynomial quadraticShape quadraticNodeGroups t y 27143631494 4675) :=
  (quadratic_actual_degree t hy).selected

theorem cubic_selected (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    Nonempty (SelectedPolynomial cubicShape cubicNodeGroups t y 141186386926 44847) :=
  (cubic_actual_degree t hy).selected

namespace SelectedPolynomial

variable (w : SelectedPolynomial s g t y a b)

def rows (i : Fin (Fintype.card (Column (s.band t)))) : ℤ × ℕ :=
  (scannedNode g (w.rowIndex i).1,(w.rowIndex i).2.val)

def cols (j : Fin (Fintype.card (Column (s.band t)))) : ℤ × ℕ := columnLabel (w.colIndex j)

noncomputable def denominator : ℕ := commonDenominator (rowFactorial w.rows) w.quotient

theorem denominator_pos : 0 < w.denominator := commonDenominator_pos (rowFactorial_pos w.rows) _

theorem denominator_dvd : w.denominator ∣ rowFactorial w.rows :=
  ⟨_,(commonDenominator_split _ w.quotient).symm⟩

theorem small_cost (S p : ℕ) (hp : p.Prime) (hS : ∀ i, (w.rowIndex i).2.val ≤ S) :
    w.denominator.factorization p ≤ p.log S * ∑ j, (w.cols j).2 :=
  quotient_prime_cost w.rowIndex (scannedNode g) w.cols w.quotient _ S p hp hS w.raw_eq

theorem level_cost (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hm : ∀ v, w.count v ≤ p^2) (H : Finset ℕ) :
    w.denominator.factorization p ≤ (primeLevelBudget w.rows w.colIndex p H).toNat :=
  quotient_prime_level_bound w.rowIndex (scannedNode g) w.colIndex w.quotient _ p hp hp2
    (fun i => (w.rowIndex i).2.isLt.trans_le (hm _)) w.raw_eq H

theorem residue_cost (p saving : ℕ) (hp : p.Prime) (hm : ∀ v, w.count v ≤ p^2)
    (hcredit : 2*(saving : ℤ) ≤ residueSurplus w.count w.cols hp.pos) :
    w.denominator.factorization p ≤ (∑ j, (w.cols j).2) - nodePairOrder (scannedNode g) w.count - saving :=
  quotient_prime_residue_saving w.rowIndex (scannedNode g) w.cols _ p saving w.quotient hp hm w.raw_eq hcredit

end SelectedPolynomial

end PiPolynomialValues.FourPeriod
