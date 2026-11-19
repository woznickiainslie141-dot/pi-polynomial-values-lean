module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

@[expose] public section

namespace PiPolynomialValues

open Polynomial Filter

/-- Maximum of the absolute integer coefficients. The zero polynomial has height zero. -/
def height (P : Polynomial ℤ) : ℕ := P.support.sup (fun i => (P.coeff i).natAbs)

theorem coeff_natAbs_le_height (P : Polynomial ℤ) (i : ℕ) :
    (P.coeff i).natAbs ≤ height P := by
  by_cases hi : i ∈ P.support
  · exact Finset.le_sup (f := fun j => (P.coeff j).natAbs) hi
  · simp [Polynomial.notMem_support_iff.mp hi]

theorem height_pos {P : Polynomial ℤ} (hP : P ≠ 0) : 0 < height P := by
  have hlead : P.coeff P.natDegree ≠ 0 := by
    simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hP
  exact (Int.natAbs_pos.mpr hlead).trans_le (coeff_natAbs_le_height P _)

theorem finite_bounded_height (d B : ℕ) :
    {P : Polynomial ℤ | P.natDegree ≤ d ∧ height P ≤ B}.Finite := by
  classical
  let box := Finset.Icc (-(B : ℤ)) (B : ℤ)
  let decode (a : Fin (d + 1) → ↥box) : Polynomial ℤ :=
    Polynomial.ofFn (d + 1) (fun i => (a i : ℤ))
  apply (Set.finite_range decode).subset
  rintro P ⟨hd, hB⟩
  have mem_box (i : Fin (d + 1)) : P.coeff i ∈ box := by
    apply Finset.mem_Icc.mpr
    apply abs_le.mp
    rw [← Int.natCast_natAbs]
    exact_mod_cast (coeff_natAbs_le_height P i).trans hB
  refine ⟨fun i => ⟨P.coeff i, mem_box i⟩, ?_⟩
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hd)

noncomputable def value (ξ : ℝ) (P : Polynomial ℤ) : ℝ := P.eval₂ (Int.castRingHom ℝ) ξ

/-- Uniform at the specified exponent, including all small heights and reducible inputs. -/
def Endpoint (ξ : ℝ) (d : ℕ) (w : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ d →
    c * (height P : ℝ) ^ (-w) ≤ |value ξ P|

def approximants (ξ : ℝ) (d : ℕ) (t : ℝ) : Set (Polynomial ℤ) :=
  {P | P ≠ 0 ∧ P.natDegree ≤ d ∧ 0 < |value ξ P| ∧ |value ξ P| < (height P : ℝ) ^ (-t)}

/-- Extended-real supremum of exponents admitting infinitely many distinct polynomials. -/
noncomputable def omega (ξ : ℝ) (d : ℕ) : EReal :=
  sSup ((fun t : ℝ => (t : EReal)) '' {t | (approximants ξ d t).Infinite})

theorem Endpoint.of_le_degree {ξ : ℝ} {d e : ℕ} {w : ℝ}
    (h : Endpoint ξ d w) (he : e ≤ d) : Endpoint ξ e w := by
  obtain ⟨c, hc, hP⟩ := h
  exact ⟨c, hc, fun P hne hdeg => hP P hne (hdeg.trans he)⟩

theorem Endpoint.weaken {ξ w u : ℝ} {d : ℕ} (h : Endpoint ξ d w) (hwu : w ≤ u) :
    Endpoint ξ d u := by
  obtain ⟨c, hc, hP⟩ := h
  refine ⟨c, hc, fun P hne hd => ?_⟩
  have hH : (1 : ℝ) ≤ height P := by exact_mod_cast Nat.succ_le_of_lt (height_pos hne)
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hH (neg_le_neg hwu)) hc.le).trans (hP P hne hd)

theorem Endpoint.finite_approximants {ξ w t : ℝ} {d : ℕ}
    (h : Endpoint ξ d w) (ht : w < t) : (approximants ξ d t).Finite := by
  obtain ⟨c, hc, hP⟩ := h
  have small : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(t - w)) < c :=
    ((tendsto_rpow_neg_atTop (sub_pos.mpr ht)).comp tendsto_natCast_atTop_atTop).eventually_lt_const hc
  obtain ⟨K, hK⟩ := eventually_atTop.1 small
  apply (finite_bounded_height d K).subset
  rintro P ⟨hne, hd, _, hclose⟩
  refine ⟨hd, ?_⟩
  by_contra! hlarge
  have hH : (0 : ℝ) < height P := by exact_mod_cast height_pos hne
  have heq : (height P : ℝ) ^ (-(t - w)) * (height P : ℝ) ^ (-w) =
      (height P : ℝ) ^ (-t) := by
    rw [← Real.rpow_add hH]
    congr 1
    ring
  have hlt := mul_lt_mul_of_pos_right (hK (height P) hlarge.le) (Real.rpow_pos_of_pos hH (-w))
  rw [heq] at hlt
  exact (not_lt_of_ge (hP P hne hd)) (hclose.trans hlt)

theorem Endpoint.omega_le {ξ w : ℝ} {d : ℕ} (h : Endpoint ξ d w) : omega ξ d ≤ (w : EReal) := by
  apply sSup_le
  rintro _ ⟨t, hinf, rfl⟩
  apply EReal.coe_le_coe
  exact le_of_not_gt fun hgt => hinf (h.finite_approximants hgt)

/-- With no exact zero, the finite exceptional set at an exponent can be absorbed into
    a single positive constant, including when the exceptional set is empty. -/
theorem endpoint_of_finite_approximants {ξ w : ℝ} {d : ℕ}
    (hzero : ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ d → value ξ P ≠ 0)
    (hfin : (approximants ξ d w).Finite) : Endpoint ξ d w := by
  classical
  let ratio (P : Polynomial ℤ) := |value ξ P| / (height P : ℝ) ^ (-w)
  let S : Finset ℝ := insert 1 (hfin.toFinset.image ratio)
  have h1 : (1 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have hS : S.Nonempty := ⟨1, h1⟩
  have hpos (y : ℝ) (hy : y ∈ S) : 0 < y := by
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact zero_lt_one
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hne, _, hval, _⟩ := hfin.mem_toFinset.mp hP
      have hH : (0 : ℝ) < height P := by exact_mod_cast height_pos hne
      exact div_pos hval (Real.rpow_pos_of_pos hH _)
  refine ⟨S.min' hS, hpos _ (S.min'_mem hS), fun P hne hd => ?_⟩
  have hH : (0 : ℝ) < height P := by exact_mod_cast height_pos hne
  have hpow := Real.rpow_pos_of_pos hH (-w)
  by_cases hP : P ∈ approximants ξ d w
  · have hr : ratio P ∈ S :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem ratio (hfin.mem_toFinset.mpr hP))
    exact (le_div_iff₀ hpow).mp (S.min'_le _ hr)
  · have hbig : (height P : ℝ) ^ (-w) ≤ |value ξ P| :=
      le_of_not_gt fun hlt => hP ⟨hne, hd, abs_pos.mpr (hzero P hne hd), hlt⟩
    calc
      S.min' hS * (height P : ℝ) ^ (-w) ≤ 1 * (height P : ℝ) ^ (-w) :=
        mul_le_mul_of_nonneg_right (S.min'_le _ h1) hpow.le
      _ ≤ |value ξ P| := by simpa only [one_mul] using hbig

/-- A strictly stronger omega estimate from another method implies the old endpoint
    as soon as exact zeros have been excluded for the indicated degrees. -/
theorem endpoint_of_omega_lt {ξ w : ℝ} {d : ℕ}
    (hzero : ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ d → value ξ P ≠ 0)
    (hw : omega ξ d < (w : EReal)) : Endpoint ξ d w := by
  apply endpoint_of_finite_approximants hzero
  by_contra hinf
  have hle : (w : EReal) ≤ omega ξ d := le_sSup ⟨w, hinf, rfl⟩
  exact (not_le_of_gt hw) hle


end PiPolynomialValues

