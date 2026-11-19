module

public import OddPiPowers.PolynomialValues.FourPeriod.ColumnResiduePrefix
public import OddPiPowers.PolynomialValues.FourPeriod.EntryDifference
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Taking all forward differences in each actual layer and residue is
an integral determinant-one column operation in any enumeration. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

private theorem det_one_of_column_grades {R K : Type*} [CommRing R] {n : ℕ}
    (tag : Fin n → K) (grade : Fin n → ℕ) (T : Matrix (Fin n) (Fin n) R)
    (hi : Function.Injective (fun i => (tag i,grade i))) (hd : ∀ i, T i i = 1)
    (hs : ∀ i j, T i j ≠ 0 → tag i = tag j ∧ grade i ≤ grade j) : T.det = 1 := by
  classical
  rw [Matrix.det_apply']
  refine (sum_eq_single 1 ?_ ?_).trans ?_
  · intro σ _ hne
    have hz : ∃ i, T (σ i) i = 0 := by
      by_contra! hall
      have hle (i : Fin n) (_ : i ∈ univ) : grade (σ i) ≤ grade i := (hs _ _ (hall i)).2
      have he := (sum_eq_sum_iff_of_le hle).mp (Equiv.sum_comp σ grade)
      exact hne (Equiv.ext (fun i => hi (Prod.ext (hs _ _ (hall i)).1 (he i (mem_univ _)))))
    obtain ⟨i,hh⟩ := hz
    rw [prod_eq_zero (f := fun j => T (σ j) j) (mem_univ i) hh,mul_zero]
  · simp
  · simp [hd]

def differenceCoefficient (k i : ℕ) : ℤ := (-1 : ℤ)^(k-i)*k.choose i

noncomputable def differenceMatrix {R : Type*} [CommRing R] {J n : ℕ} {U : Fin J → ℕ}
    (d : Fin n ≃ Column U) : Matrix (Fin n) (Fin n) R := Matrix.of fun i j =>
  if columnClass (d i) = columnClass (d j) ∧ columnOrder (d i) ≤ columnOrder (d j) then
    ((differenceCoefficient (columnOrder (d j)) (columnOrder (d i)) : ℤ) : R) else 0

theorem differenceMatrix_det {R : Type*} [CommRing R] {J n : ℕ} {U : Fin J → ℕ}
    (d : Fin n ≃ Column U) : (differenceMatrix (R := R) d).det = 1 := by
  apply det_one_of_column_grades (fun i => columnClass (d i)) (fun i => columnOrder (d i))
  · exact columnClass_order_injective.comp d.injective
  · intro i
    simp [differenceMatrix,differenceCoefficient]
  · intro i j h
    by_contra hneg
    exact h (by simp [differenceMatrix,hneg])

private theorem predecessor_sum {R : Type*} [CommRing R] {J n : ℕ} {U : Fin J → ℕ}
    (d : Fin n ≃ Column U) (c : Column U) (f : Fin n → R) :
    (∑ j, f j * differenceMatrix (R := R) d j (d.symm c)) =
      ∑ k : Fin (columnOrder c+1), f (d.symm (columnPredecessor c k)) *
        ((differenceCoefficient (columnOrder c) k.val : ℤ) : R) := by
  classical
  let pre (k : Fin (columnOrder c+1)) := d.symm (columnPredecessor c k)
  have ho (k) : columnOrder (d (pre k)) = k.val := by
    dsimp only [pre]
    rw [d.apply_symm_apply,columnPredecessor_order]
  have hc (k) : columnClass (d (pre k)) = columnClass c := by
    dsimp only [pre]
    rw [d.apply_symm_apply,columnPredecessor_class]
  have hinj : Function.Injective pre := by
    intro x y h
    apply Fin.ext
    rw [← ho x,← ho y,h]
  let g (j : Fin n) := f j*differenceMatrix (R := R) d j (d.symm c)
  change ∑ j, g j = _
  calc
    _ = ∑ j ∈ univ.image pre, g j := by
      symm
      apply sum_subset (subset_univ _)
      intro j _ hn
      have hneg : ¬ (columnClass (d j) = columnClass c ∧ columnOrder (d j) ≤ columnOrder c) := by
        rintro ⟨hclass,hord⟩
        let k : Fin (columnOrder c+1) := ⟨columnOrder (d j),by omega⟩
        apply hn
        refine mem_image.mpr ⟨k,mem_univ _,d.injective (columnClass_order_injective (Prod.ext ?_ ?_))⟩
        · exact (hc k).trans hclass.symm
        · exact ho k
      simp [g,differenceMatrix,hneg]
    _ = ∑ k, g (pre k) := sum_image (fun x _ y _ h => hinj h)
    _ = _ := by
      apply sum_congr rfl
      intro k _
      have hle : k.val ≤ columnOrder c := Nat.le_of_lt_succ k.isLt
      simp only [g,differenceMatrix,Matrix.of_apply,d.apply_symm_apply,hc,ho,hle,true_and,
        if_true,ite_true,le_refl,and_self]
      rfl

theorem column_difference_det {R : Type*} [CommRing R] {J n : ℕ} {U : Fin J → ℕ}
    (d : Fin n ≃ Column U) (f : Fin n → Fin J → ℤ → R) :
    (Matrix.of fun i j => ((fwdDiff (4 : ℤ))^[columnOrder (d j)]) (f i (d j).1) (columnStart (d j))).det =
      (Matrix.of fun i j => f i (d j).1 (d j).2.val).det := by
  let A := Matrix.of fun i j => f i (d j).1 (d j).2.val
  have he : (Matrix.of fun i j => ((fwdDiff (4 : ℤ))^[columnOrder (d j)]) (f i (d j).1) (columnStart (d j))) =
      A * differenceMatrix d := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply,← d.symm_apply_apply j]
    rw [predecessor_sum]
    simp only [d.apply_symm_apply,Matrix.of_apply,fwdDiff_iter_eq_sum_shift]
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro k _
    have hval (c : Column U) : f i (d (d.symm c)).1 (d (d.symm c)).2.val = f i c.1 c.2.val :=
      congrArg (fun b : Column U => f i b.1 b.2.val) (d.apply_symm_apply c)
    simp only [A,Matrix.of_apply,hval,columnPredecessor,differenceCoefficient,
      nsmul_eq_mul,zsmul_eq_mul]
    ring
  rw [he,Matrix.det_mul,differenceMatrix_det,mul_one]

end PiPolynomialValues.FourPeriod
