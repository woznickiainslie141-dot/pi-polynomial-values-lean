module

public import OddPiPowers.PolynomialValues.Numerics.ActualTailBudget
public import OddPiPowers.PolynomialValues.Numerics.SlabEligibility

/-! Pointwise budgets on the actual denominator. Both estimates retain
their full signed savings after a common shape baseline is introduced. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset PrimeWindow

def primeBase (s : Shape) (g : List (List ℤ)) (K t : ℕ) := baseCoefficient s*t+baseError s g K
def rowPadding (s : Shape) (g : List (List ℤ)) := g.flatten.length*(s.widths.length+1)

variable {s : Shape} {g : List (List ℤ)} {K t a b : ℕ} {y : ℂ}

theorem PrimeShapeData.finite_levels (D : PrimeShapeData s g K) (w : SelectedPolynomial s g t y a b)
    (ht : 0 < t) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hm : ∀ v, w.count v ≤ p^2)
    (H : Finset ℕ) :
    let N := s.massUnit*t
    (w.denominator.factorization p : ℝ) +
      ∑ u ∈ H, (N : ℝ)*(s.totalWidthQ : ℝ)*s.netTailValue (u+1) ((p : ℝ)/N) ≤
      (primeBase s g K t : ℝ) + (H.card : ℝ)*rowPadding s g := by
  let N := s.massUnit*t
  have ho : originOrder w.rows = nodePairOrder (scannedNode g) w.count :=
    originOrder_prefix_eq (scannedNode g) w.count w.rowIndex
  have hj : (∑ j, ((w.colIndex j).1.val : ℤ)) = ((∑ j, (w.cols j).2 : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    rfl
  have hc := w.level_cost_int p hp hp2 hm H
  rw [primeLevelBudget_counts,hj,ho,sum_sub_distrib] at hc
  have hb : ((∑ j, (w.cols j).2 : ℕ) : ℤ) ≤ (nodePairOrder (scannedNode g) w.count : ℤ) + primeBase s g K t := by
    exact_mod_cast (show (∑ j, (w.cols j).2) ≤ nodePairOrder (scannedNode g) w.count+primeBase s g K t
      by simpa only [primeBase,Nat.add_assoc] using D.baseline w)
  have hi : (w.denominator.factorization p : ℤ) +
      ∑ u ∈ H, ((columnLevelCount w.colIndex p (u+1) : ℤ)-rowLevelCount w.rows p (u+1)) ≤ primeBase s g K t := by
    rw [sum_sub_distrib]
    omega
  have hi' : (w.denominator.factorization p : ℝ) +
      ∑ u ∈ H, ((columnLevelCount w.colIndex p (u+1) : ℝ)-rowLevelCount w.rows p (u+1)) ≤ primeBase s g K t := by
    exact_mod_cast hi
  have he (u : ℕ) : (N : ℝ)*(s.totalWidthQ : ℝ)*s.netTailValue (u+1) ((p : ℝ)/N) ≤
      ((columnLevelCount w.colIndex p (u+1) : ℝ)-rowLevelCount w.rows p (u+1)) + (rowPadding s g : ℝ) := by
    simpa only [N,rowPadding,Nat.cast_mul] using D.net_ramp_le w ht p (u+1) hp.pos
  have hs := sum_le_sum (s := H) (fun u _ => he u)
  rw [sum_add_distrib,sum_const,nsmul_eq_mul] at hs
  change (w.denominator.factorization p : ℝ) + ∑ u ∈ H, (N : ℝ)*(s.totalWidthQ : ℝ)*
    s.netTailValue (u+1) ((p : ℝ)/N) ≤ _
  linarith only [hi',hs]

theorem latticeSaving_upper (bs : List Box) (N p : ℕ) (hp : 0 < p) (prev : Boundary)
    (hprev : 0 ≤ prev.value ((N : ℝ)/p)) (ho : stripOrder ((N : ℝ)/p) prev bs) :
    latticeSaving bs N p ≤ (bs.map Box.gain).sum*p := by
  induction bs generalizing prev with
  | nil => simp [latticeSaving]
  | cons b bs ih =>
    obtain ⟨hb,ht,hhi,hr⟩ := ho
    have hcard : 2*(residuePoints b N p).card ≤ p :=
      (folded_lattice_card b N p hp (hprev.trans hb) hhi).trans (by simpa using card_le_univ (foldedHits b N p))
    have hh := ih b.top ((hprev.trans hb).trans ht) hr
    have hm := Nat.mul_le_mul_left b.gain hcard
    change 2*b.gain*(residuePoints b N p).card+latticeSaving bs N p ≤ (b.gain+(bs.map Box.gain).sum)*p
    rw [Nat.add_mul,Nat.mul_comm 2 b.gain,Nat.mul_assoc]
    exact Nat.add_le_add hm hh

theorem PrimeShapeData.finite_residue (D : PrimeShapeData s g K) (w : SelectedPolynomial s g t y a b)
    (p credit : ℕ) (hc : w.denominator.factorization p ≤ (∑ j, (w.cols j).2) -
      nodePairOrder (scannedNode g) w.count - credit) (hs : credit ≤ primeBase s g K t) :
    w.denominator.factorization p + credit ≤ primeBase s g K t := by
  have hb := D.baseline w
  unfold primeBase at hs ⊢
  omega

end PiPolynomialValues.FourPeriod
