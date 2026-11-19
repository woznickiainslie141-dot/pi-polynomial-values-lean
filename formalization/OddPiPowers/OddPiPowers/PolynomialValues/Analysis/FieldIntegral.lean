module

public import OddPiPowers.PolynomialValues.Analysis.FieldChord

/-! The maximum of the fields may change node inside every cell.
Endpoint upper bounds enclose its integral with one common variation
allowance over the full spatial grid. -/

@[expose] public section

namespace PiPolynomialValues

open Real Finset Set MeasureTheory

theorem integral_affine_chord {a h l r E : ℝ} (hh : 0<h) :
    (∫ x in a..a+h, chord ((x-a)/h) l r+E) = h*((l+r)/2+E) := by
  let P (x : ℝ) := (l+E)*(x-a)+(r-l)*(x-a)^2/(2*h)
  have hd (x : ℝ) : HasDerivAt P (chord ((x-a)/h) l r+E) x := by
    have h1 := (hasDerivAt_id x).sub_const a
    have H := (h1.const_mul (l+E)).add (((h1.pow 2).const_mul (r-l)).div_const (2*h))
    convert H using 1
    · rfl
    · simp only [chord,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
      field_simp
      <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((show Continuous (fun x : ℝ => chord ((x-a)/h) l r+E) by unfold chord; fun_prop).intervalIntegrable _ _)]
  dsimp [P]
  field_simp
  <;> ring

theorem field_cell_integral {V ι : Type*} [Fintype ι] {h : ℝ} (hh : 0<h) (i : ℕ)
    (e : ι → ℕ) (d : V → ι → ℝ) (B : ι → ℝ) (hB : ∀ v k, |d v k|≤B k) (s b : V → ℝ)
    (l r : ℝ) (hl : ∀ v, meshField h (s v) (b v) e (d v) (i*h)≤l)
    (hr : ∀ v, meshField h (s v) (b v) e (d v) (((i : ℝ)+1)*h)≤r)
    (g : C(ℝ,ℝ)) (hg : ∀ x ∈ Set.Icc ((i : ℝ)*h) (((i : ℝ)+1)*h),
      ∃ v, g x ≤ meshField h (s v) (b v) e (d v) x) :
    (∫ x in ((i : ℝ)*h)..(((i : ℝ)+1)*h), g x) ≤
      h*((l+r)/2+∑ k, B k*cellAllowance h (nearestCell (e k) i)) := by
  let a := (i : ℝ)*h
  let E := ∑ k, B k*cellAllowance h (nearestCell (e k) i)
  have he : ((i : ℝ)+1)*h=a+h := by dsimp [a]; ring
  rw [he,← integral_affine_chord (a := a) hh]
  apply intervalIntegral.integral_mono_on (by change a≤a+h; linarith) (g.continuous.intervalIntegrable _ _)
    ((show Continuous (fun x : ℝ => chord ((x-a)/h) l r+E) by unfold chord; fun_prop).intervalIntegrable _ _)
  intro x hx
  obtain ⟨v,hv⟩ := hg x (by simpa only [he] using hx)
  let u := (x-a)/h
  have hu : 0≤u := div_nonneg (sub_nonneg.mpr hx.1) hh.le
  have hu1 : u≤1 := (div_le_one hh).mpr (by linarith [hx.2])
  have hx' : a+u*h=x := by dsimp [u]; field_simp; ring
  have H := meshField_chord hh hu hu1 i e (d v) B (hB v) (s v) (b v) l r (hl v) (hr v)
  exact hv.trans (by simpa only [← show a=(i : ℝ)*h from rfl,hx'] using H)

theorem field_sum_allowance {ι : Type*} [Fintype ι] {h T : ℝ} (hh : 0≤h) (hT : 0≤T)
    (K : ℕ) (e : ι → ℕ) (he : ∀ k, e k≤K) (B : ι → ℝ) (hB : ∀ k, 0≤B k)
    (value trap : ℕ → ℝ) (hc : ∀ i<K, value i≤trap i+T*h*∑ k, B k*cellAllowance h (nearestCell (e k) i)) :
    (∑ i ∈ range K, value i) ≤ (∑ i ∈ range K, trap i)+
      T*(∑ k, B k)*(h^2*(5+Real.log K)/4) := by
  apply (sum_le_sum (fun i hi => hc i (mem_range.mp hi))).trans
  rw [sum_add_distrib]
  apply add_le_add_right
  rw [← mul_sum,sum_comm]
  calc
    _ = T*∑ k, B k*(h*∑ i ∈ range K, cellAllowance h (nearestCell (e k) i)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ T*∑ k, B k*(h^2*(5+Real.log K)/4) := by
      apply mul_le_mul_of_nonneg_left _ hT
      exact sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (total_chord_allowance hh (he k)) (hB k))
    _ = _ := by rw [← sum_mul,mul_assoc]

theorem spatial_mesh_log : Real.log 80000 ≤ 17 := by
  have he := Real.log_le_log (by norm_num : 0 < (80000 : ℝ))
    (by norm_num : (80000 : ℝ)≤2^17)
  rw [Real.log_pow] at he
  norm_num only [Nat.cast_ofNat] at he
  linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))]

end PiPolynomialValues
