module

public import OddPiPowers.PolynomialValues.Numerics.PackedBitwise

/-! Pointwise maxima of complete mesh fields can be checked by word
operations even when the maximizing node changes on every sample. -/

@[expose] public section

namespace PiPolynomialValues

def packedMax (w n : ℕ) (x y : ℤ) := y+packedPositive w n (x-y)

theorem packedMax_sound (w n : ℕ) (x y : ℕ → ℤ)
    (h : ∀ i<n, -(2:ℤ)^w≤x i-y i ∧ x i-y i<(2:ℤ)^w) :
    packedMax w n (packedSum ((2:ℤ)^(w+1)) n x) (packedSum ((2:ℤ)^(w+1)) n y)=
      packedSum ((2:ℤ)^(w+1)) n (fun i => max (x i) (y i)) := by
  rw [packedMax,← packedSum_sub,packedPositive_sound _ _ _ h,← packedSum_add]
  congr 1
  funext i
  omega

def maxWithFloor {α : Type*} (q : ℤ) (val : α → ℤ) (xs : List α) : ℤ :=
  xs.foldr (fun a z => max (val a) z) q

theorem maxWithFloor_ge {α : Type*} (q : ℤ) (val : α → ℤ) (xs : List α) {a : α} (ha : a∈xs) :
    val a≤maxWithFloor q val xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h|h
    · subst a; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem maxWithFloor_range {α : Type*} {A : ℤ} (hA : 0≤A) (val : α → ℤ)
    (xs : List α) (ha : ∀ x∈xs, |val x|≤A) : |maxWithFloor (-A) val xs|≤A := by
  induction xs with
  | nil => simpa [maxWithFloor,abs_of_nonneg hA]
  | cons x xs ih =>
    have h₀ := abs_le.mp (ha x (by simp))
    have h₁ := abs_le.mp (ih (fun y hy => ha y (List.mem_cons_of_mem _ hy)))
    rw [abs_le]
    change -A≤max (val x) (maxWithFloor (-A) val xs) ∧ max (val x) (maxWithFloor (-A) val xs)≤A
    omega

def packedMaxList {α : Type*} (w n : ℕ) (A : ℤ) (word : α → ℤ) (rows : List α) : ℤ :=
  rows.foldr (fun a z => packedMax w n (word a) z) (-A*packedOnes ((2:ℤ)^(w+1)) n)

theorem packedMaxList_sound {α : Type*} (w n : ℕ) {A : ℤ} (hA : 0≤A) (hb : 2*A<(2:ℤ)^w)
    (word : α → ℤ) (val : α → ℕ → ℤ) (rows : List α)
    (hw : ∀ x∈rows, word x=packedSum ((2:ℤ)^(w+1)) n (val x))
    (hv : ∀ x∈rows, ∀ k<n, |val x k|≤A) :
    packedMaxList w n A word rows=packedSum ((2:ℤ)^(w+1)) n
      (fun k => maxWithFloor (-A) (fun x => val x k) rows) := by
  have hgt : 1<(2 : ℤ)^(w+1) := by rw [pow_succ]; have := pow_pos (by decide : (0:ℤ)<2) w; omega
  induction rows with
  | nil => exact (packedSum_const hgt n (-A)).symm
  | cons a rows ih =>
    have hrec := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
      (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    change packedMax w n (word a) (packedMaxList w n A word rows)=_
    rw [hw a (by simp),hrec]
    apply packedMax_sound
    intro k hk
    have h₀ := abs_le.mp (hv a (by simp) k hk)
    have h₁ := abs_le.mp (maxWithFloor_range hA (fun x => val x k) rows
      (fun y hy => hv y (List.mem_cons_of_mem _ hy) k hk))
    omega

end PiPolynomialValues
