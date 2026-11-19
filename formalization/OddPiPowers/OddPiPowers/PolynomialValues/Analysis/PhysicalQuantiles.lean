module

public import OddPiPowers.PolynomialValues.Analysis.QuantileMoment
public import OddPiPowers.PolynomialValues.Numerics.QuantileCuts

/-! The certified rational cuts realize the tail mass and first moment
for the actual signed frequency bands. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset MeasureTheory

noncomputable def QuantileCut.location (c : QuantileCut) (s : Shape) : ℝ :=
  (c.numerator : ℝ)/((c.slope : ℝ)*s.massUnit)

theorem scaled_tsub {a b : ℕ} {D : ℝ} (h : 0 < D) :
    max 0 ((a : ℝ)/D-(b : ℝ)/D)=((a-b : ℕ) : ℝ)/D := by
  rcases le_total a b with hab|hba
  · rw [Nat.sub_eq_zero_of_le hab,Nat.cast_zero,zero_div,max_eq_left]
    exact sub_nonpos.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hab) h.le)
  · rw [Nat.cast_sub hba,sub_div,max_eq_right]
    exact sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hba) h.le)

theorem sum_get_real {A : Type*} (l : List A) (f : A → ℝ) :
    (∑ i : Fin l.length, f (l.get i))=(l.map f).sum := by
  rw [← Fin.sum_ofFn]
  exact congrArg List.sum (List.map_ofFn.symm.trans (congrArg (List.map f) (List.ofFn_get l)))

theorem sum_get_nat {A : Type*} (l : List A) (f : A → ℕ) :
    (∑ i : Fin l.length, f (l.get i))=(l.map f).sum := by
  rw [← Fin.sum_ofFn]
  exact congrArg List.sum (List.map_ofFn.symm.trans (congrArg (List.map f) (List.ofFn_get l)))

theorem band_cut_masses (s : Shape) (c : QuantileCut) (hs : 0 < s.massUnit) (hc : 0 < c.slope) :
    (∑ j : Fin s.widths.length, max 0 (((s.widths.get j : ℝ)/10000)-c.location s))=
      (c.massNumerator s : ℝ)/((c.slope : ℝ)*s.massUnit) ∧
    (∑ j : Fin s.widths.length, max 0 (((s.widths.get j : ℝ)/10000)^2-(c.location s)^2)/2)=
      (c.twiceMomentNumerator s : ℝ)/(2*((c.slope : ℝ)*s.massUnit)^2) := by
  let D := (c.slope : ℝ)*s.massUnit
  let A (w : ℕ) := c.slope*w*s.rows.sum
  have hD : 0 < D := by dsimp [D]; positivity
  have he (w : ℕ) : (w : ℝ)/10000=(A w : ℝ)/D := by
    apply (div_eq_div_iff (by norm_num) hD.ne').mpr
    simp only [A,D,Shape.massUnit,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have H (w : ℕ) : max 0 ((w : ℝ)/10000-c.location s)=((A w-c.numerator : ℕ) : ℝ)/D := by
    rw [he,QuantileCut.location]
    exact scaled_tsub hD
  have K (w : ℕ) : max 0 (((w : ℝ)/10000)^2-(c.location s)^2)/2=
      ((A w^2-c.numerator^2 : ℕ) : ℝ)/(2*D^2) := by
    rw [he,QuantileCut.location,div_pow,div_pow]
    change max 0 ((A w : ℝ)^2/D^2-(c.numerator : ℝ)^2/D^2)/2=_
    rw [← Nat.cast_pow,← Nat.cast_pow,scaled_tsub (sq_pos_of_pos hD)]
    ring
  constructor
  · simp only [H,← sum_div,← Nat.cast_sum,sum_get_nat s.widths (fun w => A w-c.numerator)]
    rfl
  · simp only [K,← sum_div,← Nat.cast_sum,sum_get_nat s.widths (fun w => A w^2-c.numerator^2)]
    rfl

theorem actual_quantile_tail (s : Shape) (c : QuantileCut) (k common : ℕ) (hs : 0 < s.massUnit)
    (hc : cutTest s common (c,k)=true) :
    c.location s*((s.rightMass k : ℝ)/s.massUnit)+
      (∑ j : Fin s.widths.length, ∫ x in -((s.widths.get j : ℝ)/10000)..((s.widths.get j : ℝ)/10000),
        max 0 (x-c.location s))=(c.twiceMomentNumerator s : ℝ)/(2*((c.slope : ℝ)*s.massUnit)^2) := by
  obtain ⟨hsl,_,_,hm⟩ := of_decide_eq_true hc
  have hq : 0≤c.location s := by unfold QuantileCut.location; positivity
  obtain ⟨hM,hT⟩ := band_cut_masses s c hs hsl
  rw [hm,Nat.cast_mul,mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hsl.ne')] at hM
  rw [← hM,← hT,mul_sum,← sum_add_distrib]
  exact sum_congr rfl (fun j _ => threshold_band_moment hq (by positivity))

end PiPolynomialValues.FourPeriod
