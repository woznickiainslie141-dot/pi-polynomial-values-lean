module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.Analysis.Complex.Basic

/-! At a nonzero base point a, substituting a exp(w) measures exactly the
algebraic multiplicity of a polynomial root at a. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

noncomputable def exponentialPath (a : ℂ) : ℂ[X] →+* PowerSeries ℂ :=
  eval₂RingHom (PowerSeries.C : ℂ →+* PowerSeries ℂ) (PowerSeries.C a * PowerSeries.exp ℂ)

theorem constantCoeff_exponentialPath (a : ℂ) (p : ℂ[X]) :
    PowerSeries.constantCoeff (exponentialPath a p) = p.eval a := by
  rw [exponentialPath, coe_eval₂RingHom, hom_eval₂, PowerSeries.constantCoeff_comp_C,
    map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_exp, mul_one, eval₂_id]

theorem order_exponentialPath_linear {a : ℂ} (ha : a ≠ 0) :
    (exponentialPath a (X - C a)).order = 1 := by
  have h : exponentialPath a (X - C a) = PowerSeries.C a * PowerSeries.exp ℂ - PowerSeries.C a := by
    simp only [exponentialPath, coe_eval₂RingHom, eval₂_sub, eval₂_X, eval₂_C]
  rw [h]
  apply (PowerSeries.order_eq_nat (n := 1)).mpr
  constructor
  · simpa only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_exp,
      Nat.factorial_one, Nat.cast_one, div_one, map_one, mul_one, PowerSeries.coeff_C,
      one_ne_zero, ite_false, sub_zero] using ha
  · intro i hi
    have : i = 0 := by omega
    subst i
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem order_exponentialPath {a : ℂ} (ha : a ≠ 0) {p : ℂ[X]} (hp : p ≠ 0) :
    (exponentialPath a p).order = (p.rootMultiplicity a : ℕ∞) := by
  obtain ⟨q, he, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  have hv : q.eval a ≠ 0 := fun h => hq (dvd_iff_isRoot.mpr h)
  have hq0 : (exponentialPath a q).order = 0 := by
    apply le_antisymm _ zero_le
    apply PowerSeries.order_le 0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_exponentialPath]
  conv_lhs => rw [he, map_mul, map_pow, PowerSeries.order_mul, PowerSeries.order_pow,
    order_exponentialPath_linear ha, hq0]
  simp

theorem contact_sum_le_degree (S : Finset ℂ) (p : ℂ[X]) (hp : p ≠ 0)
    (m : ℂ → ℕ) (ha : ∀ a ∈ S, a ≠ 0)
    (hm : ∀ a ∈ S, (m a : ℕ∞) ≤ (exponentialPath a p).order) :
    ∑ a ∈ S, m a ≤ p.natDegree := by
  classical
  calc
    _ ≤ ∑ a ∈ S, p.roots.count a := Finset.sum_le_sum fun a haS => by
      have h := hm a haS
      rw [order_exponentialPath (ha a haS) hp] at h
      simpa only [Polynomial.count_roots] using (ENat.natCast_le_natCast.mp h)
    _ ≤ ∑ a ∈ S ∪ p.roots.toFinset, p.roots.count a :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => Nat.zero_le _)
    _ = p.roots.card := Multiset.sum_count_eq_card (fun a h => Finset.mem_union_right _ (Multiset.mem_toFinset.mpr h))
    _ ≤ _ := p.card_roots'

end PiPolynomialValues.FourPeriod
