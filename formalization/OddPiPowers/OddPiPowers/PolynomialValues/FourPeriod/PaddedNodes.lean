module

public import OddPiPowers.PolynomialValues.FourPeriod.SelectedNodes
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.Nodup
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Fill a short residue group with distinct dummy translations, each of
order zero, to obtain a square Vandermonde matrix at that base point. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def paddedNode (rows : List ℤ) (bound i : ℕ) : ℤ :=
  if h : i < rows.length then rows[i] else (bound : ℤ)+(i : ℤ)+1

theorem paddedNode_injective {rows : List ℤ} {bound : ℕ}
    (hn : rows.Nodup) (hb : ∀ v ∈ rows, v ≤ (bound : ℤ)) :
    Function.Injective (paddedNode rows bound) := by
  intro i j h
  by_cases hi : i < rows.length <;> by_cases hj : j < rows.length
  · rw [paddedNode, dif_pos hi, paddedNode, dif_pos hj] at h
    exact hn.getElem_inj_iff.mp h
  · have hle := hb rows[i] (List.getElem_mem hi)
    rw [paddedNode, dif_pos hi, paddedNode, dif_neg hj] at h
    omega
  · have hle := hb rows[j] (List.getElem_mem hj)
    rw [paddedNode, dif_neg hi, paddedNode, dif_pos hj] at h
    omega
  · rw [paddedNode, dif_neg hi, paddedNode, dif_neg hj] at h
    omega

theorem padded_sum_take {α : Type*} (rows : List α) (f : α → ℕ) (n : ℕ) :
    (∑ i : Fin n, if h : i.val < rows.length then f rows[i.val] else 0) =
      ((rows.take n).map f).sum := by
  induction rows generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Fin.sum_univ_succ]
      simpa [Nat.succ_lt_succ_iff, List.take_succ_cons] using congrArg (f x + ·) (ih n)

noncomputable def fourthBase (r : Fin 4) : ℂ := Complex.I^r.val

theorem fourthBase_ne_zero (r : Fin 4) : fourthBase r ≠ 0 := pow_ne_zero _ Complex.I_ne_zero

theorem fourthBase_injective : Function.Injective fourthBase := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num [fourthBase, pow_succ, Complex.ext_iff] at *

theorem node_base_eq {r : Fin 4} {v : ℤ} (h : v%4 = (r.val : ℤ)) :
    (Complex.I : ℂ)^v = fourthBase r := by
  rw [Complex.I_zpow_eq_zpow_mod, h, zpow_natCast] <;> rfl

theorem node_shift_injective {ι : Type*} {y : ℂ} (hy : y ≠ 0) (v : ι → ℤ) (hv : Function.Injective v) :
    Function.Injective (fun i => (v i : ℂ)*Complex.I*y/2) := by
  intro i j he
  apply hv
  have hZ : Complex.I*y/2 ≠ 0 := div_ne_zero (mul_ne_zero Complex.I_ne_zero hy) (by norm_num)
  have eq : (v i : ℂ)*(Complex.I*y/2) = (v j : ℂ)*(Complex.I*y/2) := by
    calc
      _ = (v i : ℂ)*Complex.I*y/2 := by ring
      _ = (v j : ℂ)*Complex.I*y/2 := he
      _ = _ := by ring
  exact_mod_cast mul_right_cancel₀ hZ eq

end PiPolynomialValues.FourPeriod
