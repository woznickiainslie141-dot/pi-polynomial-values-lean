module

public import OddPiPowers.PolynomialValues.FourPeriod.ScaledPrefixes
public import OddPiPowers.PolynomialValues.FourPeriod.CutQuotient

/-! A finite degree inequality with explicit error independent of scale
for the selected integral quotient at either design. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

theorem degree_from_scaled_cut {V J n : ℕ} (node : Fin V → ℤ) (a m : Fin V → ℕ)
    (u : Fin J → ℕ) (w z t K deg : ℕ) (e : Fin n ≃ RowCandidates m)
    (d : Fin n ≃ Column (fun j => u j*t))
    (hm : ∀ v, a v*t ≤ m v+K) (hn : (∑ v, m v) = Fintype.card (Column (fun j => u j*t)))
    (hcut : (deg : ℤ) + (nodePairOrder node m : ℤ) +
      (∑ i, cutQuota (w*t) (z*t) (e i).2.val) +
      (∑ j, (bandHit (z*t) (columnLabel (d j)).1 : ℤ)) ≤ ∑ j, ((columnLabel (d j)).2 : ℤ)) :
    deg + (nodePairOrder node a + scaledGain a w z + scaledHits u z)*t ≤
      (scaledLayer u + scaledLength u)*t + (layerConstant J + V*V*K + V*(2*K+3)) := by
  have hl : (∑ j, ((columnLabel (d j)).2 : ℤ)) = ((scaledLayer u*t + layerConstant J : ℕ) : ℤ) := by
    have he := Equiv.sum_comp d (fun c => (columnLabel c).2)
    exact_mod_cast he.trans (column_layer_scaled u t)
  have hh : (∑ j, (bandHit (z*t) (columnLabel (d j)).1 : ℤ)) = ((scaledHits u z*t+J : ℕ) : ℤ) := by
    have he := Equiv.sum_comp d (fun c => bandHit (z*t) (columnLabel c).1)
    exact_mod_cast he.trans (column_hits_scaled u t z)
  have ho := nodePairOrder_scaled_lower node a m t K hm
  have hq := prefix_quota_scaled_lower a m e w z t K hm
  rw [hn,column_card_scaled] at hq
  rw [hl,hh] at hcut
  rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
  omega

def shapeRowUnits (s : Shape) (groups : List (List ℤ)) (i : Fin groups.flatten.length) : ℕ :=
  2*s.widths.sum*s.ratioAt (scannedNode groups i)

def shapeBandUnits (s : Shape) (j : Fin s.widths.length) : ℕ := s.widths.get j * s.rows.sum

theorem scanned_count_sum (s : Shape) (groups : List (List ℤ)) (t : ℕ) :
    (∑ i, scanRowCount s t (scannedNode groups i)) = (groups.flatten.map (scanRowCount s t)).sum := by
  rw [← Fin.sum_ofFn]
  apply congrArg List.sum
  calc
    _ = (List.ofFn (scannedNode groups)).map (scanRowCount s t) := List.map_ofFn.symm
    _ = _ := by
      change (List.ofFn groups.flatten.get).map _ = _
      rw [List.ofFn_get]

def ShapeDegreeWitness (s : Shape) (groups : List (List ℤ)) (t : ℕ) (y : ℂ)
    (slope error : ℕ) : Prop :=
  ∃ m : Fin groups.flatten.length → ℕ,
    (∀ i, m i ≤ scanRowCount s t (scannedNode groups i)) ∧
    (∑ v, m v) = Fintype.card (Column (s.band t)) ∧
    (∀ i, scanRowCount s t (scannedNode groups i) - m i ≤
      (∑ i, scanRowCount s t (scannedNode groups i)) - Fintype.card (Column (s.band t))) ∧
    ∃ (e : Fin (Fintype.card (Column (s.band t))) ≃ RowCandidates m)
      (d : Fin (Fintype.card (Column (s.band t))) ≃ Column (s.band t)) (q : GaussianInt[X]),
      rawDeterminant (fun i => (scannedNode groups (e i).1,(e i).2.val)) (fun j => columnLabel (d j)) =
        X ^ nodePairOrder (scannedNode groups) m * q ∧
      q.eval₂ GaussianInt.toComplex y ≠ 0 ∧ q.natDegree ≤ slope*t+error

theorem shape_degree_witness {s : Shape} {groups : List (List ℤ)} {t : ℕ} {y : ℂ}
    {w z K slope error : ℕ}
    (hw : HasCutQuotient (fun i => scanRowCount s t (scannedNode groups i)) (scannedNode groups)
      (columnLabel (U := s.band t)) (w*t) y)
    (hz : z ≤ w)
    (hex : (groups.flatten.map (scanRowCount s t)).sum ≤ Fintype.card (Column (s.band t))+K)
    (hsl : scaledLayer (shapeBandUnits s) + scaledLength (shapeBandUnits s) ≤
      nodePairOrder (scannedNode groups) (shapeRowUnits s groups) + scaledGain (shapeRowUnits s groups) w z +
      scaledHits (shapeBandUnits s) z + slope)
    (her : layerConstant s.widths.length + groups.flatten.length*groups.flatten.length*K +
      groups.flatten.length*(2*K+3) ≤ error) : ShapeDegreeWitness s groups t y slope error := by
  obtain ⟨m,hm,hn,hdef,e,d,q,hd,hq,hcut⟩ := hw
  refine ⟨m,hm,hn,hdef,e,d,q,hd,hq,?_⟩
  have ha (v) : shapeRowUnits s groups v * t ≤ m v + K := by
    have hh := hdef v
    rw [scanned_count_sum] at hh
    change scanRowCount s t (scannedNode groups v) - m v ≤ _ at hh
    have hr : scanRowCount s t (scannedNode groups v) =
        shapeRowUnits s groups v * t + (s.widths.length+1) := by
      unfold scanRowCount shapeRowUnits
      ring
    rw [hr] at hh
    omega
  have hh := degree_from_scaled_cut (scannedNode groups) (shapeRowUnits s groups) m (shapeBandUnits s)
    w z t K q.natDegree e d ha hn (hcut (z*t) (Nat.mul_le_mul_right t hz))
  have hs := Nat.mul_le_mul_right t hsl
  simp only [Nat.add_mul] at hs hh
  omega

end PiPolynomialValues.FourPeriod
