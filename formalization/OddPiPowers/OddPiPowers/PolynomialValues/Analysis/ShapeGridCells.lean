module

public import OddPiPowers.PolynomialValues.Analysis.PricedBandCells
public import OddPiPowers.PolynomialValues.Numerics.CellEnvelope

/-! Align the actual signed integer columns with the 80,000 physical cells
on the subsequence indexed by multiples of four. An endpoint column is
included at both extremes of each band. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter
open scoped Topology

theorem band_hit_sum (w : ℕ) (hw : w≤10000) (F : ℕ → ℝ) :
    (∑ i ∈ range 80000, ((bandSpan w).hit i : ℝ)*F i)=∑ j ∈ range (2*(4*w)), F (40000-4*w+j) := by
  have hs : (range 80000).filter (fun i => 40000-4*w ≤ i ∧ i < 40000+4*w)=Ico (40000-4*w) (40000+4*w) := by
    ext i
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  have he (i : ℕ) : ((bandSpan w).hit i : ℝ)*F i=
      if 40000-4*w ≤ i ∧ i < 40000+4*w then F i else 0 := by
    unfold bandSpan GridSpan.hit
    split_ifs <;> simp
  simp only [he,← sum_filter,hs,sum_Ico_eq_sum_range,show 40000+4*w-(40000-4*w)=2*(4*w) by omega]

def physicalCell (M : ℕ) (x : ℤ) := (40000+x/(M : ℤ)).toNat

noncomputable def signedGridBand (D W M : ℕ) (G : ℕ → C(ℝ,ℝ)) : ℝ :=
  ((D*M : ℕ) : ℝ)⁻¹*∑ x ∈ Icc (-((W*M : ℕ) : ℤ)) ((W*M : ℕ) : ℤ),
    G (physicalCell M x) ((x : ℝ)*((D*M : ℕ) : ℝ)⁻¹)

theorem physical_band_limit (w : ℕ) (hw : w≤10000) (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (G : ℕ → C(ℝ,ℝ)) :
    Tendsto (fun t => signedGridBand 40000 (4*w) (M t) G) atTop
      (𝓝 (∑ i ∈ range 80000, ((bandSpan w).hit i : ℝ)*gridCellIntegral (G i) i)) := by
  let F (z : ℤ) := G (40000+z).toNat
  have H := priced_band_limit 40000 (4*w) (by decide) M hM F
  rw [band_hit_sum w hw]
  have hg (l : ℕ) : (40000+((l : ℤ)-(4*w : ℕ))).toNat=40000-4*w+l := by omega
  have hL (l : ℕ) : (((l : ℝ)-(4*w : ℕ))/40000)=((40000-4*w+l : ℕ) : ℝ)/40000-1 := by
    rw [Nat.cast_add,Nat.cast_sub (by omega)]; push_cast; ring
  have hR (l : ℕ) : (((l : ℝ)+1-(4*w : ℕ))/40000)=(((40000-4*w+l : ℕ) : ℝ)+1)/40000-1 := by
    rw [Nat.cast_add,Nat.cast_sub (by omega)]; push_cast; ring
  simp only [F,hg,Nat.cast_ofNat,hL,hR] at H
  apply H.congr
  intro t
  unfold signedGridBand
  congr 1
  exact (Icc (-((4*w*M t : ℕ) : ℤ)) ((4*w*M t : ℕ) : ℤ)).sum_coe_sort
    (fun x : ℤ => G (physicalCell (M t) x) ((x : ℝ)*((40000*M t : ℕ) : ℝ)⁻¹))

theorem physical_shape_limit (s : Shape) (hs : 0 < s.rows.sum) (hw : ∀ w∈s.widths, w≤10000)
    (G : Fin s.widths.length → ℕ → C(ℝ,ℝ)) :
    Tendsto (fun t : ℕ => ((s.massUnit*(4*t) : ℕ) : ℝ)⁻¹*∑ c : Column (s.band (4*t)),
      G c.1 (physicalCell (s.rows.sum*t) c.2.val) ((c.2.val : ℝ)*((s.massUnit*(4*t) : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 (∑ j : Fin s.widths.length, ∑ i ∈ range 80000,
        ((bandSpan (s.widths.get j)).hit i : ℝ)*gridCellIntegral (G j i) i)) := by
  have H := tendsto_finsetSum (univ : Finset (Fin s.widths.length)) (fun j _ =>
    physical_band_limit (s.widths.get j) (hw _ (List.get_mem _ _)) (fun t : ℕ => s.rows.sum*t)
      (tendsto_id.const_mul_atTop' hs) (G j))
  apply H.congr
  intro t
  have hN : s.massUnit*(4*t)=40000*(s.rows.sum*t) := by unfold Shape.massUnit; ring
  rw [Fintype.sum_sigma,mul_sum,hN]
  apply sum_congr rfl
  intro j _
  simp only [signedGridBand]
  congr 1
  have hb : s.band (4*t) j=4*s.widths.get j*(s.rows.sum*t) := by unfold Shape.band; ring
  rw [(Icc (-(s.band (4*t) j : ℤ)) (s.band (4*t) j : ℤ)).sum_coe_sort
    (fun x : ℤ => G j (physicalCell (s.rows.sum*t) x) ((x : ℝ)*((40000*(s.rows.sum*t) : ℕ) : ℝ)⁻¹)),hb]

end PiPolynomialValues.FourPeriod
