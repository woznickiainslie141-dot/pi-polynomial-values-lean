module

public import OddPiPowers.PolynomialValues.FourPeriod.CoefficientBlockDivisor
public import OddPiPowers.PolynomialValues.FourPeriod.PrimeDeterminant
public import OddPiPowers.PolynomialValues.FourPeriod.Degree

/-! The collision saving and the origin order hold for the same
quotient. Only column powers whose total reaches the origin order
contribute to its coefficients. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

def blockIndex {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (θ : Equiv.Perm (Fin n)) (v : Fin V) (i : Fin (m v)) : Fin n := θ.symm (e.symm ⟨v,i⟩)

theorem sum_over_blockIndex {R : Type*} [AddCommMonoid R] {V n : ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (θ : Equiv.Perm (Fin n)) (g : Fin n → R) :
    (∑ v, ∑ i, g (blockIndex e θ v i)) = ∑ i, g i := by
  unfold blockIndex
  rw [← Fintype.sum_sigma (f := fun a : RowCandidates m => g (θ.symm (e.symm a)))]
  exact (Equiv.sum_comp (e.symm.trans θ.symm) g)

def allocatedCollisions {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (θ : Equiv.Perm (Fin n)) (cols : Fin n → ℤ × ℕ) (p : ℕ) : ℕ :=
  ∑ v, collidingPairs p (fun i => (cols (blockIndex e θ v i)).1)

theorem quotient_collision_dvd {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ) (p k Cmin : ℕ) (q : GaussianInt[X])
    (hd : rawDeterminant (fun i => (node (e i).1,(e i).2.val)) cols = X^k*q)
    (hmin : ∀ θ, Cmin ≤ allocatedCollisions e θ cols p) :
    C ((p^(Cmin+k-(∑ j, (cols j).2)) : ℕ) : GaussianInt) ∣ q := by
  classical
  let A : Matrix (Fin n) (Fin n) GaussianInt[X] := Matrix.of fun i j =>
    rawEntry (node (e i).1) (cols j).1 (e i).2.val (cols j).2
  let L := (univ : Finset (Fin n)).sup (fun j => (cols j).2)+1
  have hdeg (i j) : (A i j).natDegree < L := (rawEntry_degree _ _ _ _).trans_lt
    (Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (cols j).2) (mem_univ j)))
  apply C_dvd_quotient_of_column_terms A L hdeg k q hd
  intro h hh
  let M := columnCoefficientMatrix A (fun j => (h j).val)
  change _ ∣ M.det
  by_cases hz : M.det = 0
  · rw [hz]; exact dvd_zero _
  have hle (j : Fin n) : (h j).val ≤ (cols j).2 := by
    by_contra! ht
    apply hz
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    exact coeff_eq_zero_of_natDegree_lt ((rawEntry_degree _ _ _ _).trans_lt ht)
  let D (j : Fin n) := (cols j).2-(h j).val
  have hDs : (∑ j, D j)+(∑ j, (h j).val) = ∑ j, (cols j).2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun j _ => Nat.sub_add_cancel (hle j))
  rw [det_by_node_allocations e M]
  apply Finset.dvd_sum
  intro b _
  by_cases hb : (nodeMask e M b).det = 0
  · rw [hb]; exact dvd_zero _
  obtain ⟨θ,_,u,hu⟩ := nonzero_node_allocation e M b hb
  let P (v : Fin V) := collidingPairs p (fun i => (cols (blockIndex e θ v i)).1)
  let T (v : Fin V) := ∑ i, D (blockIndex e θ v i)
  have hT : (∑ v, T v) = ∑ j, D j := sum_over_blockIndex e θ D
  have hc : Cmin ≤ ∑ v, P v := hmin θ
  have hsplit : ∑ v, P v ≤ (∑ v, (P v-T v)) + ∑ v, T v := by
    rw [← sum_add_distrib]
    exact sum_le_sum (fun v _ => by omega)
  have hdvd (v) : (p : GaussianInt)^(P v-T v) ∣ (allocationBlock e M θ v).det := by
    let x (i : Fin (m v)) := (cols (blockIndex e θ v i)).1
    let j (i : Fin (m v)) := (cols (blockIndex e θ v i)).2
    let z (i : Fin (m v)) := (h (blockIndex e θ v i)).val
    have he : allocationBlock e M θ v = Matrix.of fun i c : Fin (m v) =>
        (rawEntry (node v) (x c) i.val (j c)).coeff (z c) := by
      apply Matrix.ext
      intro i c
      have heI : (e (e.symm ⟨v,i⟩)).2.val = i.val :=
        congrArg (fun a : RowCandidates m => a.2.val) (e.apply_symm_apply ⟨v,i⟩)
      simp only [allocationBlock,M,columnCoefficientMatrix,A,Matrix.of_apply,blockIndex,x,j,z,heI,e.apply_symm_apply]
    rw [he]
    exact coeff_node_block_dvd p (node v) x j z
  rw [hu,Nat.cast_pow]
  apply dvd_mul_of_dvd_right
  apply (pow_dvd_pow (p : GaussianInt) (by omega : Cmin+k-(∑ j, (cols j).2) ≤ ∑ v, (P v-T v))).trans
  rw [← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ (fun v _ => hdvd v)

theorem quotient_prime_collision_bound {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ) (p k Cmin E : ℕ) (q : GaussianInt[X])
    (hp : p.Prime) (hd : rawDeterminant (fun i => (node (e i).1,(e i).2.val)) cols = X^k*q)
    (hmin : ∀ θ, Cmin ≤ allocatedCollisions e θ cols p)
    (hE : (rowFactorial (fun i => (node (e i).1,(e i).2.val))).factorization p-E ≤
      Cmin+k-(∑ j, (cols j).2)) :
    (commonDenominator (rowFactorial (fun i => (node (e i).1,(e i).2.val))) q).factorization p ≤ E := by
  apply commonDenominator_prime_bound hp (rowFactorial_pos _).ne'
  have ht := quotient_collision_dvd e node cols p k Cmin q hd hmin
  rw [Nat.cast_pow,map_pow] at ht ⊢
  exact (pow_dvd_pow _ hE).trans ht

end PiPolynomialValues.FourPeriod
