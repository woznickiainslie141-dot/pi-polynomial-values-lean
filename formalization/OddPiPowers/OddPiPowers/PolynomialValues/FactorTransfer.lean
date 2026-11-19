module

public import OddPiPowers.PolynomialValues.MahlerHeight
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! A lower bound for primitive, rationally irreducible inputs extends to every
integer polynomial in the same degree range, with one positive constant. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial

theorem value_mul (ξ : ℝ) (P Q : ℤ[X]) : value ξ (P * Q) = value ξ P * value ξ Q :=
  eval₂_mul ..

private theorem constant_measure_bound {ξ w b : ℝ} {P : ℤ[X]} (hw : 0 ≤ w)
    (hn : P ≠ 0) (hd : P.natDegree = 0) :
    b ^ P.natDegree * measure P ^ (-w) ≤ |value ξ P| := by
  have h1 := one_le_measure hn
  have heq : measure P = |value ξ P| := by
    obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hd
    simp only [measure_C, value, eval₂_C, Int.coe_castRingHom]
  rw [hd, pow_zero, one_mul]
  exact (Real.rpow_le_one_of_one_le_of_nonpos h1 (neg_nonpos.mpr hw)).trans (heq ▸ h1)

/-- The exponent is preserved through content and repeated factors. -/
theorem endpoint_of_primitive_irreducible {ξ w : ℝ} {d : ℕ} (hw : 0 ≤ w)
    (h : ∃ c : ℝ, 0 < c ∧ ∀ P : ℤ[X], P.IsPrimitive →
      Irreducible (P.map (Int.castRingHom ℚ)) → 0 < P.natDegree → P.natDegree ≤ d →
        c * (height P : ℝ) ^ (-w) ≤ |value ξ P|) : Endpoint ξ d w := by
  obtain ⟨c, hc, hirr⟩ := h
  let K := (2 : ℝ) ^ d
  let b := min 1 (c * K ^ (-w))
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : 0 < b := lt_min zero_lt_one (mul_pos hc (Real.rpow_pos_of_pos hK _))
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbase (P : ℤ[X]) (hi : Irreducible P) (hd : P.natDegree ≤ d) :
      b ^ P.natDegree * measure P ^ (-w) ≤ |value ξ P| := by
    by_cases h0 : P.natDegree = 0
    · exact constant_measure_bound hw hi.ne_zero h0
    have hprim := hi.isPrimitive h0
    have hH : 0 < (height P : ℝ) := by exact_mod_cast height_pos hi.ne_zero
    have hM := (P.mapMahlerMeasure_nonneg (Int.castRingHom ℂ))
    have hHK : (height P : ℝ) ≤ K * measure P := (height_le_two_pow_mul_measure P).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd) hM)
    calc
      b ^ P.natDegree * measure P ^ (-w) ≤ (c * K ^ (-w)) * measure P ^ (-w) :=
        mul_le_mul_of_nonneg_right ((pow_le_of_le_one hb.le hb1 h0).trans (min_le_right _ _))
          (Real.rpow_nonneg hM _)
      _ = c * (K * measure P) ^ (-w) := by rw [Real.mul_rpow hK.le hM, mul_assoc]
      _ ≤ c * (height P : ℝ) ^ (-w) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hH hHK (neg_nonpos.mpr hw)) hc.le
      _ ≤ _ := hirr P hprim ((IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hi)
        (Nat.pos_of_ne_zero h0) hd
  have hall (P : ℤ[X]) : P ≠ 0 → P.natDegree ≤ d →
      b ^ P.natDegree * measure P ^ (-w) ≤ |value ξ P| := by
    induction P using WfDvdMonoid.induction_on_irreducible with
    | zero => exact fun hn => (hn rfl).elim
    | unit P hu => exact fun hn _ => constant_measure_bound hw hn (natDegree_eq_zero_of_isUnit hu)
    | mul Q P hQ hi ih =>
      intro _ hd
      rw [natDegree_mul hi.ne_zero hQ] at hd ⊢
      rw [pow_add, measure_mul, Real.mul_rpow (mapMahlerMeasure_nonneg P _)
        (mapMahlerMeasure_nonneg Q _), value_mul, abs_mul, mul_mul_mul_comm]
      exact mul_le_mul (hbase P hi (by omega)) (ih hQ (by omega))
        (mul_nonneg (pow_nonneg hb.le _) (Real.rpow_nonneg (mapMahlerMeasure_nonneg Q _) _))
        (abs_nonneg _)
  let D := ((d + 1 : ℕ) : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨b ^ d * D ^ (-w), mul_pos (pow_pos hb _) (Real.rpow_pos_of_pos hD _), ?_⟩
  intro P hn hd
  have hM : 0 < measure P := zero_lt_one.trans_le (one_le_measure hn)
  have hH : 0 ≤ (height P : ℝ) := Nat.cast_nonneg _
  calc
    b ^ d * D ^ (-w) * (height P : ℝ) ^ (-w) = b ^ d * (D * height P) ^ (-w) := by
      rw [Real.mul_rpow hD.le hH, mul_assoc]
    _ ≤ b ^ P.natDegree * measure P ^ (-w) :=
      mul_le_mul (pow_le_pow_of_le_one hb.le hb1 hd)
        (Real.rpow_le_rpow_of_nonpos hM (measure_le_degree_mul_height hd) (neg_nonpos.mpr hw))
        (Real.rpow_nonneg (mul_nonneg hD.le hH) _) (pow_nonneg hb.le _)
    _ ≤ _ := hall P hn hd

end PiPolynomialValues
