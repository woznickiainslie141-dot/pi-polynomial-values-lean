module

public import OddPiPowers.PolynomialValues.Analysis.DesignFields
public import OddPiPowers.PolynomialValues.Analysis.AllocationMoments

/-! Average the reference inequalities with the actual angular mixture,
then pass from the prescribed angular slopes to the analytic paths on
the same column allocation. -/

@[expose] public section

namespace PiPolynomialValues

open Finset FourPeriod

theorem AngleDesign.weightAt_add (D : AngleDesign) (θ : ℝ) (f g : AngleLabel → ℝ) :
    D.weightAt θ (fun t => f t+g t)=D.weightAt θ f+D.weightAt θ g := by
  simp only [weightAt,realMix,list_field_sum,mul_add,sum_add_distrib]

theorem AngleDesign.weightAt_mul (D : AngleDesign) (θ a : ℝ) (f : AngleLabel → ℝ) :
    D.weightAt θ (fun t => a*f t)=a*D.weightAt θ f := by
  simpa using D.weightAt_sum θ (fun _ : Unit => a) (fun _ : Unit => f)

theorem AngleDesign.weightAt_const (D : AngleDesign) (θ a : ℝ) (h : D.weightAt θ (fun _ => 1)=1) :
    D.weightAt θ (fun _ => a)=a := by
  simpa only [mul_one,h] using D.weightAt_mul θ a (fun _ => 1)

theorem AngleDesign.average_reference_bounds {V : ℕ} (D : AngleDesign) (s : Shape) (arcs : List ArcRow)
    (hd : D.valid s arcs=true) (θ : ℝ) (hθ : D.weightAt θ (fun _ => 1)=1)
    (X : Fin V → ℝ) (f : Fin V → AngleLabel → ℝ) (fee cost : AngleLabel → ℝ) (E M L ε : ℝ)
    (H : ∀ t∈D.labels, (∑ u, X u*f u t)+E+M*fee t≤L*cost t+ε) :
    (∑ u, X u*D.weightAt θ (f u))+E+M*D.weightAt θ fee≤L*D.weightAt θ cost+ε := by
  have h := D.weightAt_mono s arcs hd θ H
  simpa only [D.weightAt_add,D.weightAt_mul,D.weightAt_sum,D.weightAt_const θ _ hθ] using h

theorem linear_path_errors {V : ℕ} (X f g d : Fin V → ℝ) {ε : ℝ}
    (h : ∀ u, |f u-g u-d u|≤ε) :
    (∑ u, X u*f u)≤(∑ u, X u*g u)+(∑ u, X u*d u)+ε*(∑ u, |X u|) := by
  have H (u : Fin V) : X u*f u≤X u*g u+X u*d u+ε*|X u| := by
    have hh := mul_le_mul_of_nonneg_left (h u) (abs_nonneg (X u))
    rw [← abs_mul] at hh
    linarith only [(le_abs_self _).trans hh]
  simpa only [sum_add_distrib,← mul_sum] using sum_le_sum (s := univ) (fun u _ => H u)

theorem boundary_allocation_bound {n V K : ℕ} (m : Fin V → ℕ) (d : ((u : Fin V) × Fin (m u)) ≃ Fin n)
    (y : Fin n → FrequencyInterval) {N : ℝ} (hN : 0<N) (v : Fin V → ℤ)
    (f g : Fin V → ℝ) (δ q : Fin K → ℝ) (hδ : ∀ k, 0≤δ k) {ε : ℝ} (hε : 0≤ε)
    (h : ∀ u, |f u-g u-orderedDirection δ (v u)|≤ε) :
    let P := allocationCharge m d y N
    (∑ u, P u (linearFrequency (f u))) ≤ (∑ u, firstMoment (P u)*g u)+
      (∑ k, δ k*tailCap m v (fun j => (y j : ℝ)) N k.val (q k))+ε*((n : ℝ)/N) := by
  intro P
  have H := linear_path_errors (fun u => firstMoment (P u)) f g (fun u => orderedDirection δ (v u)) h
  have ht := allocated_first_tail m d y hN v δ q hδ
  have he := mul_le_mul_of_nonneg_left (allocated_first_abs m d y hN) hε
  rw [show (∑ u, orderedDirection δ (v u)*firstMoment (allocationCharge m d y N u))=
      ∑ u, firstMoment (P u)*orderedDirection δ (v u) from sum_congr rfl (fun _ _ => mul_comm _ _)] at ht
  simp only [evaluate_linear]
  rw [show (∑ u, f u*firstMoment (P u))=∑ u, firstMoment (P u)*f u from sum_congr rfl (fun _ _ => mul_comm _ _)]
  exact H.trans (add_le_add (add_le_add le_rfl ht) he)

end PiPolynomialValues
