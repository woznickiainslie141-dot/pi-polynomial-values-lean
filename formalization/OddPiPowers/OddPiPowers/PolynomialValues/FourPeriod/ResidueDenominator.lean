module

public import OddPiPowers.PolynomialValues.FourPeriod.CollisionDenominator
public import OddPiPowers.PolynomialValues.FourPeriod.ResiduePairs
public import OddPiPowers.PolynomialValues.FourPeriod.ResidueCollisions
public import OddPiPowers.PolynomialValues.FourPeriod.LargePrimeEntry

/-! The signed convex collision surplus uses only the actual frequency
multiset and prefix sizes. It applies to every allocation simultaneously. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

theorem rowFactorial_large_floor {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (p : ℕ) (hp : p.Prime) (hm : ∀ v, m v ≤ p^2) :
    ((rowFactorial (fun i => (node (e i).1,(e i).2.val))).factorization p : ℤ) =
      ∑ v, quotientSum p (m v) := by
  rw [rowFactorial_factorization,Nat.cast_sum]
  let f (a : RowCandidates m) := (a.2.val.factorial.factorization p : ℤ)
  change ∑ i, f (e i) = _
  rw [Equiv.sum_comp e f,Fintype.sum_sigma]
  apply sum_congr rfl
  intro v _
  calc
    _ = ∑ i : Fin (m v), ((i.val/p : ℕ) : ℤ) := by
      apply sum_congr rfl
      intro i _
      change ((i.val.factorial.factorization p : ℕ) : ℤ) = ((i.val/p : ℕ) : ℤ)
      exact congrArg (Nat.cast : ℕ → ℤ) (factorial_large p i.val hp (i.isLt.trans_le (hm v)))
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => ((i/p : ℕ) : ℤ)) (m v)

theorem column_residues_across_blocks {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (θ : Equiv.Perm (Fin n)) (cols : Fin n → ℤ × ℕ) {p : ℕ} (hp : 0 < p) (r : Fin p) :
    (∑ v, residueMultiplicity hp (fun i => (cols (blockIndex e θ v i)).1) r) =
      residueMultiplicity hp (fun i => (cols i).1) r := by
  let g (i : Fin n) := if residueTag hp (cols i).1 = r then 1 else 0
  have he := sum_over_blockIndex e θ g
  simpa only [g,Finset.sum_boole,residueMultiplicity,Nat.cast_id] using he

def residueSurplus {V n : ℕ} (m : Fin V → ℕ) (cols : Fin n → ℤ × ℕ) {p : ℕ} (hp : 0 < p) : ℤ :=
  ∑ r : Fin p, collisionTwice
    ((residueMultiplicity hp (fun i => (cols i).1) r : ℤ) - ∑ v, ((m v/p : ℕ) : ℤ)) V

theorem residueSurplus_le_allocated {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (θ : Equiv.Perm (Fin n)) (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ)
    (p : ℕ) (hp : p.Prime) (hm : ∀ v, m v ≤ p^2) :
    residueSurplus m cols hp.pos ≤ 2*((allocatedCollisions e θ cols p : ℤ) -
      (rowFactorial (fun i => (node (e i).1,(e i).2.val))).factorization p) := by
  let x (v : Fin V) (i : Fin (m v)) := (cols (blockIndex e θ v i)).1
  let f (v : Fin V) := residueMultiplicity hp.pos (x v)
  have hh := residue_collision_sum_le univ p hp.pos m f (fun v _ => sum_residueMultiplicity hp.pos (x v))
  have hcol (r : Fin p) : (∑ v, (f v r : ℤ)) = (residueMultiplicity hp.pos (fun i => (cols i).1) r : ℤ) := by
    exact_mod_cast column_residues_across_blocks e θ cols hp.pos r
  have hpair (v : Fin V) : (∑ r : Fin p, (f v r : ℤ)*((f v r : ℤ)-1)) =
      2*(collidingPairs p (x v) : ℤ) := (twice_collidingPairs hp.pos (x v)).symm
  simp only [card_univ,Fintype.card_fin,hcol,hpair,sum_sub_distrib,← mul_sum] at hh
  rw [rowFactorial_large_floor e node p hp hm]
  unfold allocatedCollisions
  rw [Nat.cast_sum,mul_sub]
  exact hh

theorem quotient_prime_residue_saving {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ) (k p saving : ℕ) (q : GaussianInt[X])
    (hp : p.Prime) (hm : ∀ v, m v ≤ p^2)
    (hd : rawDeterminant (fun i => (node (e i).1,(e i).2.val)) cols = X^k*q)
    (hcredit : 2*(saving : ℤ) ≤ residueSurplus m cols hp.pos) :
    let rows := fun i => (node (e i).1,(e i).2.val)
    (commonDenominator (rowFactorial rows) q).factorization p ≤ (∑ j, (cols j).2) - k - saving := by
  let F := rowFactorial (fun i => (node (e i).1,(e i).2.val))
  apply quotient_prime_collision_bound e node cols p k (F.factorization p+saving) _ q hp hd
  · intro θ
    have ht := hcredit.trans (residueSurplus_le_allocated e θ node cols p hp hm)
    change _ ≤ 2*((allocatedCollisions e θ cols p : ℤ)-(F.factorization p : ℤ)) at ht
    omega
  · change F.factorization p - ((∑ j, (cols j).2)-k-saving) ≤ F.factorization p+saving+k-_
    omega

end PiPolynomialValues.FourPeriod
