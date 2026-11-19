module

public import OddPiPowers.PolynomialValues.FactorTransfer
public import OddPiPowers.PolynomialValues.PiNonvanishing

/-! To obtain a positive constant at the endpoint it suffices to rule
out a sequence of primitive irreducibles of increasing height that
violates the bound with constant one. -/

@[expose] public section

namespace PiPolynomialValues

open Filter Polynomial Set

def PrimitiveInput (d : ℕ) (P : ℤ[X]) : Prop :=
  P.IsPrimitive ∧ Irreducible (P.map (Int.castRingHom ℚ)) ∧ 0<P.natDegree ∧ P.natDegree≤d

theorem endpoint_of_no_escaping_input {ξ w : ℝ} {d : ℕ} (hw : 0≤w)
    (hn : ∀ P : ℤ[X], P≠0 → P.natDegree≤d → value ξ P≠0)
    (hex : ∀ p : ℕ → ℤ[X], (∀ k, PrimitiveInput d (p k)) → Tendsto (fun k => height (p k)) atTop atTop →
      (∀ k, |value ξ (p k)|<(height (p k) : ℝ)^(-w)) → False) : Endpoint ξ d w := by
  classical
  let S := {P : ℤ[X] | PrimitiveInput d P ∧ |value ξ P|<(height P : ℝ)^(-w)}
  have hS : S.Finite := by
    by_contra hs
    have hu (k : ℕ) : ∃ P∈S, k<height P := by
      by_contra! h
      exact hs ((finite_bounded_height d k).subset (fun P hP => ⟨hP.1.2.2.2,h P hP⟩))
    choose p hm hh using hu
    exact hex p (fun k => (hm k).1) (tendsto_atTop.2 (fun k =>
      (eventually_ge_atTop k).mono (fun _ hl => hl.trans (hh _).le))) (fun k => (hm k).2)
  let ratio (P : ℤ[X]) := |value ξ P|/(height P : ℝ)^(-w)
  let T : Finset ℝ := insert 1 (hS.toFinset.image ratio)
  have h1 : (1:ℝ)∈T := Finset.mem_insert_self _ _
  have hT : T.Nonempty := ⟨1,h1⟩
  have hpos (a : ℝ) (ha : a∈T) : 0<a := by
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact zero_lt_one
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
    have hp := (hS.mem_toFinset.mp hP).1
    have hP' : P≠0 := fun he => by simpa [he] using hp.2.2.1
    have hH : 0<(height P : ℝ) := by exact_mod_cast height_pos hP'
    exact div_pos (abs_pos.mpr (hn P hP' hp.2.2.2)) (Real.rpow_pos_of_pos hH _)
  apply endpoint_of_primitive_irreducible hw
  refine ⟨T.min' hT,hpos _ (T.min'_mem hT),?_⟩
  intro P hp hi hdeg hd
  have hP : P≠0 := fun he => by simpa [he] using hdeg
  have hH : 0<(height P : ℝ) := by exact_mod_cast height_pos hP
  have hpow := Real.rpow_pos_of_pos hH (-w)
  by_cases h : |value ξ P|<(height P : ℝ)^(-w)
  · have hm : P∈S := ⟨⟨hp,hi,hdeg,hd⟩,h⟩
    have ht : ratio P∈T := Finset.mem_insert_of_mem (Finset.mem_image_of_mem ratio (hS.mem_toFinset.mpr hm))
    exact (le_div_iff₀ hpow).mp (T.min'_le _ ht)
  · exact (mul_le_mul_of_nonneg_right (T.min'_le _ h1) hpow.le).trans (by simpa only [one_mul] using le_of_not_gt h)

theorem measure_tendsto_of_height {d : ℕ} (p : ℕ → ℤ[X]) (hd : ∀ k, (p k).natDegree≤d)
    (hh : Tendsto (fun k => height (p k)) atTop atTop) : Tendsto (fun k => measure (p k)) atTop atTop := by
  have H : Tendsto (fun k => (height (p k) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hh
  have hk : 0<(2:ℝ)^d := by positivity
  apply tendsto_atTop_mono (f := fun k => (height (p k) : ℝ)/2^d) _ (H.atTop_div_const hk)
  intro k
  apply (div_le_iff₀ hk).mpr
  rw [mul_comm]
  exact (height_le_two_pow_mul_measure _).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (hd _)) ((p k).mapMahlerMeasure_nonneg _))

end PiPolynomialValues
