module

public import OddPiPowers.PolynomialValues.RootBudgetLimits

/-! Positive capped exponent gives exponential decay of the genuine
Taylor perturbation, including its scale factor, at the same conjugate. -/

@[expose] public section

namespace PiPolynomialValues

open Real Filter
open scoped Topology

theorem conjugate_taylor_decay {X : ℕ → ℝ} (hX : Tendsto X atTop atTop) {z : ℕ → ℂ}
    (hne : ∀ i, (π : ℂ)≠z i) {C b c : ℝ} (H : Tendsto (fun i => cappedProximity C (X i) π (z i)) atTop (𝓝 b))
    (hc : 0<c) (hcb : c≤b) {η : ℝ} (hη : 0<η) : ∀ᶠ i in atTop,
    1≤‖z i‖ ∧ ‖Complex.I*(z i-(π : ℂ))/2‖≤exp (-((c-η)*X i)) := by
  let a := min (η/2) (c/2)
  have ha : 0<a := lt_min (half_pos hη) (half_pos hc)
  have he : 0<c-a := by have := min_le_right (η/2) (c/2); dsimp [a]; linarith
  have hd : 0<η-a := by have := min_le_left (η/2) (c/2); dsimp [a]; linarith
  have hB := H.eventually (lt_mem_nhds (show c-a<b by linarith))
  have h₀ := tendsto_exp_neg_atTop_nhds_zero.comp (hX.const_mul_atTop he)
  change Tendsto (fun i => exp (-((c-a)*X i))) atTop (𝓝 0) at h₀
  let K := 1+‖(π : ℂ)‖
  have hK : 0<K := by dsimp [K]; positivity
  have hr := h₀.const_mul (2*K)
  simp only [mul_zero] at hr
  have hπ : 0<‖(π : ℂ)‖-1 := by simp [abs_of_pos pi_pos]; linarith [pi_gt_three]
  have hs := (hX.const_mul_atTop hd).eventually (eventually_ge_atTop (log K))
  filter_upwards [hX.eventually (eventually_ge_atTop 1),hB,h₀.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)),
    hr.eventually (gt_mem_nhds hπ),hs] with i hx hb hhalf hdist hbig
  have hz := conjugate_distance_bound (hne i) hx hb.le hhalf.le
  have htri := norm_sub_norm_le (π : ℂ) (z i)
  refine ⟨by change 2*K*exp (-((c-a)*X i))<‖(π : ℂ)‖-1 at hdist; change ‖(π : ℂ)-z i‖≤2*K*_ at hz
             linarith only [htri,hz,hdist],?_⟩
  have hKe : K≤exp ((η-a)*X i) := (exp_log hK) ▸ exp_le_exp.mpr hbig
  rw [norm_div,norm_mul,Complex.norm_I,one_mul,Complex.norm_ofNat,norm_sub_rev]
  calc
    ‖(π : ℂ)-z i‖/2≤K*exp (-((c-a)*X i)) := by change ‖(π : ℂ)-z i‖≤2*K*_ at hz; linarith only [hz]
    _ ≤ exp ((η-a)*X i)*exp (-((c-a)*X i)) := mul_le_mul_of_nonneg_right hKe (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

end PiPolynomialValues
