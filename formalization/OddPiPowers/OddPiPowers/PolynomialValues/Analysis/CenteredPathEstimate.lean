module

public import OddPiPowers.PolynomialValues.Analysis.PathOriginOrder
public import OddPiPowers.PolynomialValues.Analysis.PoissonMajorant

/-! Interior estimate for the exact translated determinant, with the
same admissible Taylor labels as in the expansion at the origin. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Complex Real Metric Finset

theorem column_divided_analytic (t : ℂ) (j σ : ℕ) (z : ℂ) :
    AnalyticAt ℂ (dividedRow σ (columnFunction t j)) z := by
  have H (k : ℕ) : AnalyticAt ℂ (iteratedDeriv k (columnFunction t j)) z := by
    induction k with
    | zero => rw [iteratedDeriv_zero]; unfold columnFunction; fun_prop
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  exact analyticAt_const.mul (H σ)

theorem centered_det_analytic {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ → ℂ) {z : ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) z) :
    AnalyticAt ℂ (fun w => (centeredLabelMatrix e v x j a h (fun i => p i w)).det) z := by
  have H (i c : Fin n) : AnalyticAt ℂ
      (fun w => centeredLabelMatrix e v x j a h (fun i => p i w) i c) z := by
    let b : ℂ := 2^j c*((v (e i).1 : ℂ)-(a (x c) : ℂ))^(h c).val
    let f := columnFunction (x c : ℂ) (j c-(h c).val)
    have he : (fun w => centeredLabelMatrix e v x j a h (fun i => p i w) i c) =
        (fun w => b*dividedRow (e i).2.val f (p (e i).1 w)) := by
      funext w
      rw [show f = _ from (rfl : f=columnFunction (x c : ℂ) (j c-(h c).val)),dividedRow_columnFunction]
      change b*Complex.exp _*_=b*(Complex.exp _*_)
      ring
    rw [he]
    exact analyticAt_const.mul ((column_divided_analytic _ _ _ _).comp (hp _))
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  exact fun i _ => H (σ i) i

theorem centered_path_poisson {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ → ℂ) (hp : ∀ i, AnalyticOnNhd ℂ (p i) (closedBall 0 1))
    (h0 : ∀ i, p i 0=0) {b : ℂ → ℝ} (hb : ContinuousOn b (sphere 0 1))
    (hbnd : ∀ z ∈ sphere 0 1, ‖(centeredLabelMatrix e v x j a h (fun i => p i z)).det‖ ≤ Real.exp (b z))
    {w : ℂ} (hw : ‖w‖<1) :
    ∃ q : LabelChoice (fun c => (h c).val),
      ‖(centeredLabelMatrix e v x j a h (fun i => p i w)).det‖ ≤
        ‖w‖^(labelPairs (fun c => (q c).val)-∑ i, (e i).2.val)*Real.exp (poissonMean w b) := by
  have hz : (0 : ℂ) ∈ closedBall 0 1 := by simp
  obtain ⟨q,G,hG,he⟩ := centeredLabelMatrix_factor e v x j a h p (fun i => hp i _ hz) h0
  exact ⟨q,factored_poisson_majorant (fun z hz => centered_det_analytic e v x j a h p (fun i => hp i z hz))
    hG _ he hb hbnd hw⟩

end PiPolynomialValues.FourPeriod
