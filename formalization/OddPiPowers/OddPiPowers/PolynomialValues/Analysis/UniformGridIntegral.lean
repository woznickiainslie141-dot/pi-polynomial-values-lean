module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Uniform-mesh left sums for continuous tests. Endpoint weights in an
integer band may be retained explicitly. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory Set Filter Finset
open scoped Topology Interval

theorem left_grid_integral_error (f : C(ℝ,ℝ)) (a h E : ℝ) (hh : 0 ≤ h) (m : ℕ)
    (hc : ∀ k < m, ∀ x ∈ Icc (a+k*h) (a+(k+1 : ℕ)*h), |f (a+k*h)-f x| ≤ E) :
    |h*(∑ k ∈ range m, f (a+k*h))-(∫ x in a..a+m*h, f x)| ≤ (m : ℝ)*h*E := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hi := ih (fun k hk => hc k (Nat.lt_succ_of_lt hk))
    let lo := a+(m : ℝ)*h
    let top := a+((m+1 : ℕ) : ℝ)*h
    have he : top-lo = h := by dsimp [lo,top]; push_cast; ring
    have hle : lo ≤ top := by linarith
    have hb : |h*f lo-(∫ x in lo..top, f x)| ≤ h*E := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := lo) (b := top)
        (f := fun x => f lo - f x) (C := E) (fun x hx => hc m (Nat.lt_succ_self _) x <|
          Set.Ioc_subset_Icc_self (by simpa only [Set.uIoc_of_le hle] using hx))
      rw [intervalIntegral.integral_sub intervalIntegrable_const (f.continuous.intervalIntegrable _ _),
        intervalIntegral.integral_const,smul_eq_mul,he,abs_of_nonneg hh] at h1
      exact h1.trans_eq (mul_comm _ _)
    rw [sum_range_succ,mul_add,← intervalIntegral.integral_add_adjacent_intervals
      (f.continuous.intervalIntegrable a lo) (f.continuous.intervalIntegrable lo top)]
    change |h*(∑ k ∈ range m, f (a+k*h))+h*f lo-(_+_)| ≤ _
    rw [show h*(∑ k ∈ range m, f (a+k*h))+h*f lo-((∫ x in a..lo, f x)+(∫ x in lo..top, f x)) =
      (h*(∑ k ∈ range m, f (a+k*h))-(∫ x in a..lo, f x))+(h*f lo-(∫ x in lo..top, f x)) by ring]
    apply (abs_add_le _ _).trans
    push_cast
    linarith

theorem left_grid_integral_limit {ι : Type*} {F : Filter ι} (f : C(ℝ,ℝ)) (a b : ℝ)
    (m : ι → ℕ) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) (ht : Tendsto h F (𝓝 0))
    (hab : a ≤ b) (hm : ∀ᶠ i in F, (m i : ℝ)*h i = b-a) :
    Tendsto (fun i => h i*(∑ k ∈ range (m i), f (a+k*h i))) F (𝓝 (∫ x in a..b, f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let E := ε/(b-a+1)
  have hp : 0 < b-a+1 := by linarith
  have hE : 0 < E := div_pos hε hp
  have hU := isCompact_Icc.uniformContinuousOn_of_continuous (s := Set.Icc a b) f.continuous.continuousOn
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hU E hE
  filter_upwards [hm,ht.eventually_lt_const hδ] with i hi hδi
  have hb : a+(m i : ℝ)*h i = b := by linarith
  have hc (k : ℕ) (hk : k<m i) (x : ℝ) (hx : x ∈ Set.Icc (a+k*h i) (a+(k+1 : ℕ)*h i)) :
      |f (a+k*h i)-f x| ≤ E := by
    have hseg : a+((k+1 : ℕ) : ℝ)*h i ≤ b := by
      rw [← hb]
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ (hh i)
      exact_mod_cast (show k+1 ≤ m i from hk)
    have hlo : a ≤ a+(k : ℝ)*h i := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (hh i))
    have hd : dist (a+k*h i) x < δ := by
      rw [Real.dist_eq,abs_of_nonpos (by linarith [hx.1])]
      have hs := hx.2
      push_cast at hs
      linarith
    exact (hclose (a+k*h i) ⟨hlo,hx.1.trans (hx.2.trans hseg)⟩ x
      ⟨hlo.trans hx.1,hx.2.trans hseg⟩ hd).le
  have he := left_grid_integral_error f a (h i) E (hh i) (m i) hc
  rw [hb,hi] at he
  rw [Real.dist_eq]
  apply he.trans_lt
  have heq : (b-a+1)*E = ε := by dsimp [E]; field_simp
  nlinarith only [heq,hE]

end PiPolynomialValues
