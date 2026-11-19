module

public import Mathlib.Data.List.Sort
import all Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Basic

/-! The two equal-parity four-period shapes, using integer bandwidths and row
ratios. All strict prefix inequalities are checked on the actual node arrays. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

structure Shape where
  /-- Half-bandwidths in units of one ten-thousandth of the scale. -/
  widths : List ℕ
  /-- Row ratios for nodes 0 through V. Negative nodes reflect the positive nodes. -/
  ratios : List ℕ
deriving DecidableEq

def quadraticShape : Shape :=
  ⟨[10000, 9433, 8788, 8119, 7405, 6632, 5810, 5535, 4595, 3438, 1692],
   [10000, 9471, 8567, 6294]⟩

def cubicShape : Shape :=
  ⟨[10000, 9710, 9363, 9010, 8650, 8283, 7907, 7515, 7110, 6685, 6235, 6097,
    5610, 5077, 4487, 3820, 2993, 1917],
   [10000, 9812, 9660, 9112, 8138, 6653, 3701]⟩

/-- Rows in increasing order of the signed node v from -V through V. -/
def Shape.rows (s : Shape) : List ℕ := s.ratios.tail.reverse ++ s.ratios

/-- Ratios in one signed residue class, largest first. -/
def Shape.residueRows (s : Shape) (r : ℕ) : List ℕ :=
  let V := s.ratios.length - 1
  let indices : List ℕ := (List.range s.rows.length).filter
    (fun (i : ℕ) => ((i : ℤ) - (V : ℤ)) % 4 == (r : ℤ))
  (indices.map fun i => s.rows[i]?.getD 0).insertionSort (· ≥ ·)

def Shape.selected (s : Shape) (k : ℕ) : ℕ :=
  ((List.range 4).map (fun r => ((s.residueRows r).take k).sum)).sum

/-- For N = 10000 times the total row ratio times t, each half-bandwidth and
each desired row count is an integer. These two totals are the bandwidth and
row sides of the selection inequality at a prefix of k layers. -/
def Shape.frequencyPrefix (s : Shape) (k t : ℕ) : ℕ :=
  2 * (s.widths.take k).sum * s.rows.sum * t

def Shape.rowPrefix (s : Shape) (k t : ℕ) : ℕ :=
  2 * s.widths.sum * s.selected k * t

private def strictPrefixTable (s : Shape) : Bool :=
  (List.range (s.widths.length - 1)).all (fun j =>
    decide ((s.widths.take (j + 1)).sum * s.rows.sum < s.widths.sum * s.selected (j + 1)))

private theorem prefix_lt_of_table {s : Shape} (h : strictPrefixTable s = true)
    {k t : ℕ} (hk : 0 < k) (hlt : k < s.widths.length) (ht : 0 < t) :
    s.frequencyPrefix k t < s.rowPrefix k t := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hmem : j ∈ List.range (s.widths.length - 1) := List.mem_range.mpr (by omega)
  have hp := of_decide_eq_true (List.all_eq_true.mp h j hmem)
  change (s.widths.take (j + 1)).sum * s.rows.sum < s.widths.sum * s.selected (j + 1) at hp
  simpa only [Shape.frequencyPrefix, Shape.rowPrefix, Nat.mul_assoc] using
    Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hp (by decide : 0 < 2)) ht

theorem quadratic_prefix_lt {k t : ℕ} (hk : 0 < k) (hlt : k < quadraticShape.widths.length)
    (ht : 0 < t) : quadraticShape.frequencyPrefix k t < quadraticShape.rowPrefix k t :=
  prefix_lt_of_table (s := quadraticShape) (by decide +kernel) hk hlt ht

theorem cubic_prefix_lt {k t : ℕ} (hk : 0 < k) (hlt : k < cubicShape.widths.length)
    (ht : 0 < t) : cubicShape.frequencyPrefix k t < cubicShape.rowPrefix k t :=
  prefix_lt_of_table (s := cubicShape) (by decide +kernel) hk hlt ht

theorem quadratic_last_prefix (t : ℕ) :
    quadraticShape.frequencyPrefix quadraticShape.widths.length t =
      quadraticShape.rowPrefix quadraticShape.widths.length t := by
  exact congrArg (fun a : ℕ => a * t) (show 2 * _ * _ = 2 * _ * _ by decide +kernel)

theorem cubic_last_prefix (t : ℕ) :
    cubicShape.frequencyPrefix cubicShape.widths.length t =
      cubicShape.rowPrefix cubicShape.widths.length t := by
  exact congrArg (fun a : ℕ => a * t) (show 2 * _ * _ = 2 * _ * _ by decide +kernel)

end PiPolynomialValues.FourPeriod
