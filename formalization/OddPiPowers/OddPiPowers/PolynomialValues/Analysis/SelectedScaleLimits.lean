module

public import OddPiPowers.PolynomialValues.FourPeriod.ScannedOrder
public import OddPiPowers.PolynomialValues.Numerics.RootScaleIndex
public import OddPiPowers.PolynomialValues.Analysis.BlockAmplitude

/-! The row masses, total number of columns and polynomial overhead have
the same limits for every selected minor, even when its root varies. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Real Filter PrimeWindow
open scoped Topology

variable {ι : Type*} {F : Filter ι} {t : ι → ℕ} {s : Shape}

theorem massScale_atTop (ht : Tendsto t F atTop) (h : 0 < s.massUnit) :
    Tendsto (fun i => ((s.massUnit*t i : ℕ) : ℝ)) F atTop :=
  tendsto_natCast_atTop_atTop.comp (ht.const_mul_atTop' h)

theorem selected_length_limit (ht : Tendsto t F atTop) (hs : 0 < s.massUnit) :
    Tendsto (fun i => (Fintype.card (Column (s.band (t i))) : ℝ)/((s.massUnit*t i : ℕ) : ℝ)) F
      (𝓝 (s.totalWidthQ : ℝ)) := by
  have H := (affine_ratio_atTop (2*s.widths.sum*s.rows.sum) s.widths.length s.massUnit 0 hs).comp ht
  simp only [Nat.add_zero,Function.comp_def,← shape_column_card] at H
  have hrow : (s.rows.sum : ℝ)≠0 := by
    exact_mod_cast (show s.rows.sum≠0 by intro he; simp [Shape.massUnit,he] at hs)
  have he : (s.totalWidthQ : ℝ)=((2*s.widths.sum*s.rows.sum : ℕ) : ℝ)/(s.massUnit : ℝ) := by
    simp only [Shape.totalWidthQ,Shape.massUnit,Nat.cast_mul,Nat.cast_ofNat,Rat.cast_div,
      Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
    field_simp [hrow]
    <;> ring
  rw [he]
  exact H

theorem selected_mass_limit {g : List (List ℤ)} {K a b : ℕ} {y : ι → ℂ} (D : RowData s g K)
    (ht : Tendsto t F atTop) (w : ∀ i, SelectedPolynomial s g (t i) (y i) a b) (v : Fin g.flatten.length) :
    Tendsto (fun i => ((w i).count v : ℝ)/((s.massUnit*t i : ℕ) : ℝ)) F
      (𝓝 (rowRate s (s.ratioAt (scannedNode g v)))) := by
  let N (i : ι) := ((s.massUnit*t i : ℕ) : ℝ)
  let A := rowRate s (s.ratioAt (scannedNode g v))
  have hN := massScale_atTop ht D.mass_pos
  have H := (tendsto_inv_atTop_zero.comp hN).const_mul (K : ℝ)
  simp only [mul_zero] at H
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ H
  filter_upwards [hN.eventually (eventually_gt_atTop 0)] with i hi
  change dist (((w i).count v : ℝ)/N i) A ≤ (K : ℝ)*(N i)⁻¹
  have hq : ((w i).count v : ℝ)/N i-A=(((w i).count v : ℝ)-A*N i)/N i := by
    field_simp [show N i≠0 from hi.ne']
  rw [Real.dist_eq,← div_eq_mul_inv,hq,abs_div,abs_of_pos hi]
  exact div_le_div_of_nonneg_right (D.selected_count_close (w i) v) hi.le

theorem columnOverhead_limit {N : ι → ℝ} {n : ι → ℕ} {L K : ℝ} (J : ℕ)
    (hN : Tendsto N F atTop) (hn : Tendsto (fun i => (n i : ℝ)/N i) F (𝓝 L)) (hL : 0 < L) (hK : 1≤K) :
    Tendsto (fun i => columnOverhead K (n i) J/N i) F (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp hN
  change Tendsto (fun i => (N i)⁻¹) F (𝓝 0) at hi
  have H : Tendsto (fun i => (K+(n i : ℝ)^2+1)/(N i)^2) F (𝓝 (L^2)) := by
    have H := ((hi.pow 2).const_mul K).add (hn.pow 2) |>.add (hi.pow 2)
    simp only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_add,add_zero] at H
    apply H.congr
    intro i
    simp only [div_eq_mul_inv,← inv_pow,mul_pow]
    ring
  have h₁ := ((continuousAt_log (pow_ne_zero 2 hL.ne')).tendsto.comp H).mul hi
  have h₂ : Tendsto (fun i => log (N i)/N i) F (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hN
  have h := (((hi.const_mul (log 2+log K)).add h₁).add (h₂.const_mul 2)).const_mul (J : ℝ)
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [hN.eventually (eventually_gt_atTop 0)] with i hi
  change (J : ℝ)*((log 2+log K)*(N i)⁻¹+log ((K+(n i : ℝ)^2+1)/(N i)^2)*(N i)⁻¹+2*(log (N i)/N i))=_
  rw [log_div (by linarith [sq_nonneg (n i : ℝ)]) (pow_ne_zero 2 hi.ne'),log_pow]
  unfold columnOverhead
  ring

end PiPolynomialValues.FourPeriod
