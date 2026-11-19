module

public import OddPiPowers.PolynomialValues.FourPeriod.SelectedPolynomial
public import OddPiPowers.PolynomialValues.Analysis.CenteredExpansion
public import OddPiPowers.PolynomialValues.Analysis.PolynomialUnitCircle
public import OddPiPowers.PolynomialValues.NormalizedResultant

/-! All analytic bounds apply to the same Gaussian polynomial that was
selected at the real root and whose denominator and degree were bounded. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod.SelectedPolynomial

open Finset Polynomial

variable {s : Shape} {g : List (List ℤ)} {t a b : ℕ} {y : ℂ} (w : SelectedPolynomial s g t y a b)

theorem norm_identity (z : ℂ) :
    ‖z‖^(nodePairOrder (scannedNode g) w.count)*‖w.integral.eval₂ GaussianInt.toComplex z‖ =
      w.denominator*‖normalizedDetValue w.rows w.cols z‖ := by
  have hr : w.rows=(fun i => (scannedNode g (w.rowIndex i).1,(w.rowIndex i).2.val)) := by funext i; rfl
  have hc : w.cols=(fun j => columnLabel (w.colIndex j)) := by funext j; rfl
  simpa only [norm_mul,norm_pow,Complex.norm_natCast,denominator,hr,hc] using congrArg norm (w.identity z)

theorem unit_path_matrix (z : ℂ) :
    normalizedDetValue w.rows w.cols z =
      (pathMatrix w.rowIndex (fun c => (w.cols c).1) (fun c => (w.cols c).2)
       (fun v _ => (scannedNode g v : ℂ)*Complex.I*z/2)
       (fun v c => (2 : ℂ)^(w.cols c).2*Complex.I^(scannedNode g v*(w.cols c).1))).det := rfl

theorem reduced_eval_of_unit_bound {C : ℝ}
    (h : ∀ z : ℂ, ‖z‖=1 → ‖normalizedDetValue w.rows w.cols z‖≤C) (z : ℂ) :
    reducedEvaluation w.integral z ≤ w.denominator*C := by
  let P := w.integral.map GaussianInt.toComplex
  have H := polynomial_normalized_bound P (C := w.denominator*C) (fun ζ hζ => by
    have Hζ := w.norm_identity ζ
    rw [hζ,one_pow,one_mul] at Hζ
    change ‖(w.integral.map GaussianInt.toComplex).eval ζ‖ ≤ _
    rw [eval_map,Hζ]
    exact mul_le_mul_of_nonneg_left (h ζ hζ) (Nat.cast_nonneg _)) z
  simpa only [reducedEvaluation,P,eval_map,natDegree_map_eq_of_injective GaussianInt.toComplex_injective] using H

theorem eval_le_centered_labels (hU : Antitone (s.band t)) (center : ℤ → ℤ) (z : ℂ) (hz : 1≤‖z‖) :
    let x c := (w.colIndex c).2.val
    let j c := (w.colIndex c).1.val
    let δ := Complex.I*(z-(Real.pi : ℂ))/2
    ‖w.integral.eval₂ GaussianInt.toComplex z‖ ≤ w.denominator*
      ∑ h : LabelChoice j, ‖labelCoefficient j h δ‖*
        ‖(centeredLabelMatrix w.rowIndex (scannedNode g) x j center h (fun i => phasePoint (scannedNode g i))).det‖ := by
  intro x j δ
  have h1 := le_mul_of_one_le_left (norm_nonneg (w.integral.eval₂ GaussianInt.toComplex z))
    (one_le_pow₀ (n := nodePairOrder (scannedNode g) w.count) hz)
  apply (h1.trans_eq (w.norm_identity z)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have he := normalized_det_centered w.rowIndex hU w.colIndex (scannedNode g) z center
  change normalizedDetValue w.rows w.cols z = ∑ h : LabelChoice j, labelCoefficient j h δ*
    (centeredLabelMatrix w.rowIndex (scannedNode g) x j center h (fun i => phasePoint (scannedNode g i))).det at he
  rw [he]
  exact (norm_sum_le _ _).trans_eq (sum_congr rfl (fun i _ => norm_mul _ _))

end PiPolynomialValues.FourPeriod.SelectedPolynomial
