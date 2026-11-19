module

public import OddPiPowers.PolynomialValues.FourPeriod.Shape
import all Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring

/-! Actual signed nodes for local translations and uniform integer room in
the bandwidth contradiction, at every layer and every exact integer scale. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def Shape.ratioAt (s : Shape) (v : ℤ) : ℕ := s.ratios[v.natAbs]?.getD 0

def quadraticNodeGroups : List (List ℤ) := [[0], [1,-3], [-2,2], [-1,3]]
def cubicNodeGroups : List (List ℤ) := [[0,-4,4], [1,-3,5], [-2,2,-6,6], [-1,3,-5]]

def SignedSchedule (s : Shape) (groups : List (List ℤ)) : Prop :=
  groups.length = 4 ∧ groups.flatten.Nodup ∧
  ∀ r : Fin 4, (groups[r.val]?.getD []).all (fun v =>
      decide (v % 4 = (r.val : ℤ) ∧ v.natAbs < s.ratios.length)) = true ∧
    ((groups[r.val]?.getD []).map s.ratioAt) = s.residueRows r.val

theorem quadratic_signed_schedule : SignedSchedule quadraticShape quadraticNodeGroups := by
  unfold SignedSchedule
  decide +kernel

theorem cubic_signed_schedule : SignedSchedule cubicShape cubicNodeGroups := by
  unfold SignedSchedule
  decide +kernel

def selectedNodes (groups : List (List ℤ)) (j : ℕ) : List ℤ :=
  groups.flatMap (fun row => row.take (j+1))

def scanRowCount (s : Shape) (t : ℕ) (v : ℤ) : ℕ :=
  (2*s.widths.sum*t)*s.ratioAt v + (s.widths.length+1)

def actualContactCount (s : Shape) (groups : List (List ℤ)) (j t : ℕ) : ℕ :=
  ((selectedNodes groups j).map (fun v => scanRowCount s t v - j)).sum

private theorem sum_counts (s : Shape) (rows : List ℤ) (j t : ℕ) (hj : j ≤ s.widths.length+1) :
    (rows.map (fun v => scanRowCount s t v-j)).sum =
      (2*s.widths.sum*t)*(rows.map s.ratioAt).sum + rows.length*(s.widths.length+1-j) := by
  induction rows with
  | nil => simp
  | cons v rows ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih]
    simp only [scanRowCount, Nat.add_sub_assoc hj]
    ring

private def contactChecks (s : Shape) (groups : List (List ℤ)) (room : ℕ) : Bool :=
  (List.range s.widths.length).all fun j =>
    let rows := selectedNodes groups j
    decide (2*(s.widths.take (j+1)).sum*s.rows.sum ≤ 2*s.widths.sum*(rows.map s.ratioAt).sum ∧
      room ≤ rows.length*(s.widths.length+1-j))

private theorem frequency_room {s : Shape} {groups : List (List ℤ)} {room j : ℕ}
    (h : contactChecks s groups room = true) (hj : j < s.widths.length) (t : ℕ) :
    s.frequencyPrefix (j+1) t + room ≤ actualContactCount s groups j t := by
  have he := of_decide_eq_true (List.all_eq_true.mp h j (List.mem_range.mpr hj))
  change 2*(s.widths.take (j+1)).sum*s.rows.sum ≤ 2*s.widths.sum*((selectedNodes groups j).map s.ratioAt).sum ∧
    room ≤ (selectedNodes groups j).length*(s.widths.length+1-j) at he
  rw [actualContactCount, sum_counts _ _ _ _ (by omega)]
  apply Nat.add_le_add _ he.2
  calc
    _ ≤ (2*s.widths.sum*((selectedNodes groups j).map s.ratioAt).sum)*t := Nat.mul_le_mul_right t he.1
    _ = _ := by ring

theorem quadratic_contact_room {j : ℕ} (hj : j < quadraticShape.widths.length) (t : ℕ) :
    quadraticShape.frequencyPrefix (j+1) t + 14 ≤ actualContactCount quadraticShape quadraticNodeGroups j t :=
  frequency_room (by decide +kernel) hj t

theorem cubic_contact_room {j : ℕ} (hj : j < cubicShape.widths.length) (t : ℕ) :
    cubicShape.frequencyPrefix (j+1) t + 26 ≤ actualContactCount cubicShape cubicNodeGroups j t :=
  frequency_room (by decide +kernel) hj t

/-- Number of candidates above the required square matrix size, after all
actual node prefixes have been scanned. -/
theorem quadratic_candidate_excess (t : ℕ) :
    (quadraticNodeGroups.flatten.map (scanRowCount quadraticShape t)).sum =
      2*quadraticShape.widths.sum*quadraticShape.rows.sum*t+quadraticShape.widths.length+73 := by
  have h := sum_counts quadraticShape quadraticNodeGroups.flatten 0 t (Nat.zero_le _)
  simp only [Nat.sub_zero] at h
  rw [h]
  have he : (quadraticNodeGroups.flatten.map quadraticShape.ratioAt).sum = quadraticShape.rows.sum := by decide +kernel
  rw [he]
  change 2*quadraticShape.widths.sum*t*quadraticShape.rows.sum+7*(11+1) =
    2*quadraticShape.widths.sum*quadraticShape.rows.sum*t+11+73
  ring

theorem cubic_candidate_excess (t : ℕ) :
    (cubicNodeGroups.flatten.map (scanRowCount cubicShape t)).sum =
      2*cubicShape.widths.sum*cubicShape.rows.sum*t+cubicShape.widths.length+229 := by
  have h := sum_counts cubicShape cubicNodeGroups.flatten 0 t (Nat.zero_le _)
  simp only [Nat.sub_zero] at h
  rw [h]
  have he : (cubicNodeGroups.flatten.map cubicShape.ratioAt).sum = cubicShape.rows.sum := by decide +kernel
  rw [he]
  change 2*cubicShape.widths.sum*t*cubicShape.rows.sum+13*(18+1) =
    2*cubicShape.widths.sum*cubicShape.rows.sum*t+18+229
  ring

end PiPolynomialValues.FourPeriod
