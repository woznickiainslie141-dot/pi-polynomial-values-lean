module

public import OddPiPowers.PolynomialValues.Analysis.UnitEvaluations
public import OddPiPowers.PolynomialValues.Analysis.AngularCorrectionCost
public import OddPiPowers.PolynomialValues.Analysis.AngularDeterminant

/-! A fixed family of analytic paths has one column-overhead constant
at all scales, including every physical cell center. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Finset Metric Set Real Polynomial

theorem AnchorPlan.center_le (a : AnchorPlan) (i : ℕ) : a.center i≤(a.map Prod.snd).sum := by
  induction a with
  | nil => simp [center]
  | cons p a ih =>
    simp only [center,List.map_cons,List.sum_cons]
    split_ifs <;> omega

theorem center_norm_bound (s : Shape) (a : AnchorPlan) (t : ℕ) (x : ℤ) :
    ‖(centeredGridValue s a t x : ℂ)‖≤((a.map Prod.snd).sum : ℝ)+(s.ratios.length : ℝ) := by
  unfold centeredGridValue
  rw [Int.cast_sub]
  apply (norm_sub_le _ _).trans
  simp only [Int.cast_natCast,Complex.norm_natCast]
  exact add_le_add (by exact_mod_cast a.center_le _) (by exact_mod_cast Nat.sub_le s.ratios.length 1)

namespace EvaluationPlan

theorem increment_nodes (P : EvaluationPlan) (u : Fin P.groups.flatten.length) :
    (∑ k : Fin P.cuts.length, nodeSign k.val (scannedNode P.groups u))=scannedNode P.groups u := by
  rw [P.order.node]
  exact (of_decide_eq_true P.slopes).1 (P.order.rank u)

theorem paths (P : EvaluationPlan) {r t : ℝ} (hr : 0<r) (ht : 0≤t) (ht1 : t<1)
    (g : Fin P.cuts.length → ℂ[X]) (hg : ∀ j, (g j).eval 0=0) (u : Fin P.groups.flatten.length) :
    AnalyticOnNhd ℂ (incrementFamily r t g (scannedNode P.groups u)) (closedBall 0 1) ∧
      incrementFamily r t g (scannedNode P.groups u) 0=0 ∧
      incrementFamily r t g (scannedNode P.groups u) (r : ℂ)=phasePoint (scannedNode P.groups u) :=
  incrementFamily_spec hr ht ht1 g hg _ (P.increment_nodes u)

theorem common_path_bound (P : EvaluationPlan) (p : Fin P.groups.flatten.length → ℂ → ℂ)
    (hp : ∀ u, AnalyticOnNhd ℂ (p u) (closedBall 0 1)) :
    ∃ K : ℝ, 1≤K ∧
      (∀ (u : Fin P.groups.flatten.length) (t : ℕ) (x : ℤ),
        ‖(scannedNode P.groups u : ℂ)-(centeredGridValue P.shape P.anchor t x : ℂ)‖≤K) ∧
      (∀ (u : Fin P.groups.flatten.length) (z : ℂ), ‖z‖=1 → ‖p u z‖≤K) := by
  have H (u : Fin P.groups.flatten.length) := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn
    ((hp u).continuousOn.mono sphere_subset_closedBall)
  choose c hc using H
  let A := SelectedSequence.nodeBound P+((P.anchor.map Prod.snd).sum : ℝ)+(P.shape.ratios.length : ℝ)
  let B := ∑ u, |c u|
  have hA : 1≤A := by
    dsimp only [A]
    linarith only [SelectedSequence.nodeBound_one P,Nat.cast_nonneg (α := ℝ) (P.anchor.map Prod.snd).sum,
      Nat.cast_nonneg (α := ℝ) P.shape.ratios.length]
  refine ⟨max A B,hA.trans (le_max_left _ _),?_,?_⟩
  · intro u t x
    apply (norm_sub_le _ _).trans
    apply le_trans _ (le_max_left A B)
    exact (add_le_add (SelectedSequence.nodeBound_ge P u) (center_norm_bound P.shape P.anchor t x)).trans_eq (by dsimp [A]; ring)
  · intro u z hz
    apply (hc u z (mem_sphere_zero_iff_norm.mpr hz)).trans
    exact (le_abs_self (c u)).trans ((single_le_sum (fun j _ => abs_nonneg (c j)) (mem_univ u)).trans (le_max_right A B))

end EvaluationPlan
end PiPolynomialValues
