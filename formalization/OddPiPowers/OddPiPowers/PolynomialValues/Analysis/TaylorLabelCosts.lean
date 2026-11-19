module

public import OddPiPowers.PolynomialValues.Analysis.FiniteLabelPrice
public import OddPiPowers.PolynomialValues.Analysis.PerturbationExpansion
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The full Taylor expansion costs at most exponentially many terms in
the column count. The radius gain and its off-center price are retained
for the actual perturbation labels and the smaller interior Taylor labels. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Real

theorem labelChoice_count {n J : ℕ} (j : Fin n → ℕ) (hj : ∀ c, j c≤J) :
    Fintype.card (LabelChoice j)≤(J+1)^n := by
  change Fintype.card ((c : Fin n) → Fin (j c+1))≤_
  rw [Fintype.card_pi]
  simpa using prod_le_prod' (s := univ) (f := fun c : Fin n => j c+1) (g := fun _ => J+1)
    (fun a _ => Nat.add_le_add_right (hj a) 1)

theorem perturbation_coefficient {n J : ℕ} (j : Fin n → ℕ) (h : LabelChoice j) (hj : ∀ c, j c≤J)
    {δ : ℂ} {t : ℝ} (hd : ‖δ‖≤exp (-t)) :
    ‖labelCoefficient j h δ‖≤exp ((n : ℝ)*J*log 2-(∑ c, ((h c).val : ℝ))*t) := by
  have H (c : Fin n) : ‖((j c).choose (h c).val : ℂ)*δ^(h c).val‖≤
      exp ((J : ℝ)*log 2-((h c).val : ℝ)*t) := by
    rw [norm_mul,Complex.norm_natCast,norm_pow,sub_eq_add_neg,exp_add,exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<2),
      show -(((h c).val : ℝ)*t)=((h c).val : ℝ)*(-t) by ring,exp_nat_mul]
    exact mul_le_mul (by exact_mod_cast ((j c).choose_le_two_pow _).trans (Nat.pow_le_pow_right (by decide) (hj c)))
      (pow_le_pow_left₀ (norm_nonneg δ) hd _) (pow_nonneg (norm_nonneg δ) _) (by positivity)
  rw [labelCoefficient,norm_prod]
  apply (prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun c _ => H c)).trans_eq
  rw [← exp_sum,sum_sub_distrib,← sum_mul,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  simp only [sum_mul]

theorem radius_order_bound {r : ℝ} (hr : 0<r) (hr1 : r≤1) (a b : ℕ) :
    r^(a-b)≤exp (((b : ℝ)-(a : ℝ))*log (1/r)) := by
  have hlog : 0≤log (1/r) := log_nonneg ((le_div_iff₀ hr).mpr (by simpa using hr1))
  have ha : (a : ℝ)-(b : ℝ)≤((a-b : ℕ) : ℝ) := by
    rcases le_total b a with h|h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h,Nat.cast_zero]
      exact sub_nonpos.mpr (by exact_mod_cast h)
  calc
    r^(a-b)=exp (-((a-b : ℕ) : ℝ)*log (1/r)) := by
      rw [one_div,log_inv,neg_mul_neg,exp_nat_mul,exp_log hr]
    _ ≤ _ := exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right ha hlog])

theorem chosen_origin_price {n J : ℕ} (hn : 0<n) (j : Fin n → ℕ) (hj : ∀ c, j c≤J)
    (h : LabelChoice j) (q : LabelChoice (fun c => (h c).val)) {B c δ : ℝ}
    (hB : 0<B) (hc : 0≤c) (hδ : 0≤δ) (hhi : 2*B≤3*c+δ) :
    pricedMinimum B c δ≤
      ((∑ a, ((h a).val : ℝ))*c+(∑ a, if (h a).val=0 then (0 : ℝ) else 1)*δ)/n+
        B*(2*labelPairs (fun a => (q a).val)+(n : ℝ))/(n : ℝ)^2 := by
  let q' (a : Fin n) : Fin (J+2) := ⟨(q a).val,by
    have h₁ : (q a).val < (h a).val+1 := (q a).isLt
    have h₂ := (h a).isLt
    have h₃ := hj a
    omega⟩
  have hh := finite_priced_origin hn q' (fun a => (h a).val) (fun a => Nat.lt_succ_iff.mp (q a).isLt)
    hB hc hδ hhi
  have he : (∑ a, if (h a).val=0 then (0 : ℝ) else δ)=(∑ a, if (h a).val=0 then (0 : ℝ) else 1)*δ := by
    rw [sum_mul]
    exact sum_congr rfl (fun a _ => by split_ifs <;> simp)
  simpa only [q',sum_add_distrib,← sum_mul,he] using hh

end PiPolynomialValues.FourPeriod
