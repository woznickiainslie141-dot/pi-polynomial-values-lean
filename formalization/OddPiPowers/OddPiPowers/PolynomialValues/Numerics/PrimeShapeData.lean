module

public import OddPiPowers.PolynomialValues.FourPeriod.ActualLevelCounts
public import OddPiPowers.PolynomialValues.Numerics.SelectedRowFloors
public import OddPiPowers.PolynomialValues.Numerics.PrimeTailSound
import all Mathlib.Data.List.Sort

/-! Match the actual signed node ranks, widths and two finite moments to
the rational tables used by the two prime certificates. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset PrimeWindow

deriving instance DecidableEq for TailTerm

def nodeTerm (s : Shape) (g : List (List ℤ)) (v : Fin g.flatten.length) : TailTerm :=
  ⟨s.rowUnits (s.ratioAt (scannedNode g v)),s.massUnit,scannedRank g v⟩

def columnTerm (s : Shape) (j : Fin s.widths.length) : TailTerm := ⟨s.widths.get j,20000,j.val⟩

structure PrimeShapeData (s : Shape) (g : List (List ℤ)) (K : ℕ) : Prop extends RowData s g K where
  rank_inj : Function.Injective (fun v => (scannedNode g v % 4,scannedRank g v))
  row_terms : List.ofFn (nodeTerm s g) = s.rowTails
  column_terms : List.ofFn (columnTerm s) = s.columnTails
  rank_moment : nodePairOrder (scannedNode g) (shapeRowUnits s g) = s.geometry.rankMoment
  layer_moment : scaledLayer (shapeBandUnits s) = s.geometry.layerMoment
  moments_ordered : s.geometry.rankMoment ≤ s.geometry.layerMoment
  widths_pos : 0 < s.widths.sum

theorem quadratic_prime_shape_data : PrimeShapeData quadraticShape quadraticNodeGroups 73 := by
  refine ⟨quadratic_row_data,quadratic_ranks_injective,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem cubic_prime_shape_data : PrimeShapeData cubicShape cubicNodeGroups 229 := by
  refine ⟨cubic_row_data,cubic_ranks_injective,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

def baseCoefficient (s : Shape) := s.geometry.layerMoment-s.geometry.rankMoment

def baseError (s : Shape) (g : List (List ℤ)) (K : ℕ) :=
  layerConstant s.widths.length + g.flatten.length*g.flatten.length*K

theorem PrimeShapeData.baseline {s : Shape} {g : List (List ℤ)} {K t a b : ℕ} {y : ℂ}
    (D : PrimeShapeData s g K) (w : SelectedPolynomial s g t y a b) :
    (∑ j, (w.cols j).2) ≤ nodePairOrder (scannedNode g) w.count + baseCoefficient s*t + baseError s g K := by
  have hm (v : Fin g.flatten.length) : shapeRowUnits s g v*t ≤ w.count v+K := by
    have hd := w.deficit v
    rw [scanned_count_sum] at hd
    have hx := D.extra t
    have he : scanRowCount s t (scannedNode g v) = shapeRowUnits s g v*t+(s.widths.length+1) := by
      unfold scanRowCount shapeRowUnits
      ring
    rw [he] at hd
    omega
  have hr := nodePairOrder_scaled_lower (scannedNode g) (shapeRowUnits s g) w.count t K hm
  rw [D.rank_moment] at hr
  have hj : (∑ j, (w.cols j).2) = scaledLayer (shapeBandUnits s)*t+layerConstant s.widths.length :=
    (Equiv.sum_comp w.colIndex (fun c => (columnLabel c).2)).trans (column_layer_scaled (shapeBandUnits s) t)
  rw [hj,D.layer_moment]
  have he : s.geometry.rankMoment*t+baseCoefficient s*t = s.geometry.layerMoment*t := by
    rw [← Nat.add_mul,baseCoefficient,Nat.add_sub_of_le D.moments_ordered]
  unfold baseError
  omega

theorem PrimeShapeData.row_sum {s : Shape} {g : List (List ℤ)} {K : ℕ}
    (D : PrimeShapeData s g K) (h : ℕ) (x : ℝ) :
    (∑ v, (nodeTerm s g v).value h x) = listTail s.rowTails h x := by
  rw [← Fin.sum_ofFn,← D.row_terms]
  unfold listTail
  rw [List.map_ofFn]
  rfl

theorem PrimeShapeData.column_sum {s : Shape} {g : List (List ℤ)} {K : ℕ}
    (D : PrimeShapeData s g K) (h : ℕ) (x : ℝ) :
    (∑ j, (columnTerm s j).value h x) = listTail s.columnTails h x := by
  rw [← Fin.sum_ofFn,← D.column_terms]
  unfold listTail
  rw [List.map_ofFn]
  rfl

end PiPolynomialValues.FourPeriod
