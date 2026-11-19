module

public import OddPiPowers.PolynomialValues.Analysis.PerturbationExpansion
public import OddPiPowers.PolynomialValues.FourPeriod.Columns

/-! Lowering the derivative order inside each frequency prefix is a
unitriangular column operation for every choice of translation center. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

theorem det_lower_layers {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n → ℕ)
    (down : ∀ i, Fin (j i+1) → Fin n) (h0 : ∀ i, down i 0 = i)
    (hd : ∀ i k, j (down i k)+k.val = j i)
    (a : ∀ i, Fin (j i+1) → ℂ) (ha : ∀ i, a i 0 = 1) :
    (Matrix.of (fun i c => ∑ k, a c k*A i (down c k))).det = A.det := by
  classical
  let z : LabelChoice j := fun _ => 0
  rw [det_weighted_columns a (fun c k i => A i (down c k)),sum_eq_single z]
  · simp only [z,ha,prod_const_one,one_mul,h0,Matrix.of_apply]
    rfl
  · intro h _ hn
    let d (i : Fin n) := down i (h i)
    have hni : ¬Function.Injective d := by
      intro hi
      let e := Equiv.ofBijective d ⟨hi,Finite.surjective_of_injective hi⟩
      have hs : (∑ i, j (d i)) = ∑ i, j i := Equiv.sum_comp e j
      have ht := sum_congr (s₁ := (univ : Finset (Fin n))) rfl (fun i _ => hd i (h i))
      change (∑ i, (j (d i)+(h i).val)) = ∑ i, j i at ht
      rw [sum_add_distrib,hs] at ht
      apply hn
      funext i
      apply Fin.ext
      have hle := single_le_sum (s := (univ : Finset (Fin n))) (f := fun t => (h t).val)
        (fun _ _ => Nat.zero_le _) (mem_univ i)
      change (h i).val = 0
      omega
    obtain ⟨i,l,hne,he⟩ : ∃ i l, i ≠ l ∧ d i=d l := by
      by_contra! h
      exact hni (fun {i l} hh => by_contra fun hn => h i l hn hh)
    apply mul_eq_zero_of_right
    apply Matrix.det_zero_of_column_eq hne
    intro t
    exact congrArg (A t) he
  · simp

def lowerBandColumn {J : ℕ} {U : Fin J → ℕ} (hU : Antitone U) (c : Column U)
    (k : Fin (c.1.val+1)) : Column U :=
  let i : Fin J := ⟨c.1.val-k.val,(Nat.sub_le _ _).trans_lt c.1.isLt⟩
  ⟨i, c.2.val,by
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp c.2.property
    have hu : U c.1 ≤ U i := hU (show i ≤ c.1 from Nat.sub_le _ _)
    exact mem_Icc.mpr ⟨by omega,by omega⟩⟩

theorem lowerBandColumn_zero {J : ℕ} {U : Fin J → ℕ} (hU : Antitone U) (c : Column U) :
    lowerBandColumn hU c 0 = c := by
  apply columnLabel_injective
  apply Prod.ext
  · rfl
  · simp [lowerBandColumn,columnLabel]

noncomputable def shiftedEntry (v t : ℤ) (σ j : ℕ) (y w : ℂ) : ℂ :=
  (2 : ℂ)^j*Complex.I^(v*t)*
    (rowOperator 1 ((v : ℂ)*Complex.I*y/2+w) j (normalizedRowPolynomial σ)).eval (t : ℂ)

theorem shiftedEntry_sum (v t : ℤ) (σ j : ℕ) (y w : ℂ) :
    shiftedEntry v t σ j y w = ∑ k : Fin (j+1),
      ((j.choose k.val : ℂ)*(2*w)^k.val)*normalizedEntry v t σ (j-k.val) y := by
  rw [shiftedEntry,rowOperator_perturb,eval_finsetSum,mul_sum,← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro k _
  simp only [eval_mul,eval_C,normalizedEntry,mul_pow]
  have hk : k.val+(j-k.val) = j := Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)
  rw [show (2 : ℂ)^j = 2^k.val * 2^(j-k.val) from
    (congrArg (fun s : ℕ => (2 : ℂ)^s) hk.symm).trans (pow_add _ _ _)]
  ring

theorem det_shiftedEntry {n J : ℕ} {U : Fin J → ℕ} (hU : Antitone U) (e : Fin n ≃ Column U)
    (v : Fin n → ℤ) (σ : Fin n → ℕ) (y : ℂ) (w : ℤ → ℂ) :
    (Matrix.of (fun i c => shiftedEntry (v i) (e c).2.val (σ i) (e c).1.val y (w (e c).2.val))).det =
    (Matrix.of (fun i c => normalizedEntry (v i) (e c).2.val (σ i) (e c).1.val y)).det := by
  let A := Matrix.of (fun i c => normalizedEntry (v i) (e c).2.val (σ i) (e c).1.val y)
  let j (c : Fin n) := (e c).1.val
  let down (c : Fin n) (k : Fin (j c+1)) := e.symm (lowerBandColumn hU (e c) k)
  let a (c : Fin n) (k : Fin (j c+1)) := ((j c).choose k.val : ℂ)*(2*w (e c).2.val)^k.val
  have he : Matrix.of (fun i c => shiftedEntry (v i) (e c).2.val (σ i) (e c).1.val y (w (e c).2.val)) =
      Matrix.of (fun i c => ∑ k, a c k*A i (down c k)) := by
    ext i c
    rw [Matrix.of_apply,shiftedEntry_sum]
    simp only [A,down,Matrix.of_apply,e.apply_symm_apply]
    apply sum_congr rfl
    intro k _
    rw [show (e (e.symm (lowerBandColumn hU (e c) k))).2.val = (lowerBandColumn hU (e c) k).2.val from
      congrArg (fun p : Column U => p.2.val) (e.apply_symm_apply _)]
    rfl
  rw [he]
  refine det_lower_layers A j down ?_ ?_ a ?_
  · intro i
    simp [down,lowerBandColumn_zero]
  · intro i k
    change ((e (e.symm (lowerBandColumn hU (e i) k))).1.val)+k.val = (e i).1.val
    rw [e.apply_symm_apply]
    exact Nat.sub_add_cancel (Nat.le_of_lt_succ k.isLt)
  · intro i
    simp [a]

end PiPolynomialValues.FourPeriod
