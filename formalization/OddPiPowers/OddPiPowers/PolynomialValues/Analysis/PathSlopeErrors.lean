module

public import OddPiPowers.PolynomialValues.Analysis.IncrementPaths
public import OddPiPowers.PolynomialValues.Analysis.DirectionMoments

/-! The common analytic error on the boundary has a small actual Poisson
integral. The contribution of the positive corrections is left in the
signed quantile estimate at each boundary point. -/

@[expose] public section

namespace PiPolynomialValues

open Finset FourPeriod Polynomial Real Filter MeasureTheory Metric

noncomputable def slopeError {K : ℕ} (g : Fin K → ℂ[X]) (F : Fin K → ArcForm) (w : ℂ) :=
  ∑ k, |((g k).eval w).im-signedFold (F k).field w|

noncomputable def pathGap (r : ℝ) (g : ℂ[X]) := π/2-(g.eval (r : ℂ)).re

theorem faceSlope_sum {K : ℕ} (face : Bool) (v : ℤ) (p : Fin K → ℂ) :
    faceSlope face (∑ k, (nodeSign k.val v : ℂ)*p k)=∑ k, (nodeSign k.val v : ℝ)*faceSlope face (p k) := by
  cases face <;> simp [faceSlope,Complex.mul_re,Finset.sum_neg_distrib]

theorem family_slope_error {K : ℕ} {r t : ℝ} (hr : 0<r) (ht : 0≤t) (ht1 : t<1)
    (g : Fin K → ℂ[X]) (hg : ∀ k, ((g k).eval (r : ℂ)).im=0) (F : Fin K → ArcForm)
    (w : ℂ) (hw : ‖w‖=1) (hi : w.im≠0) (v : ℤ) :
    |faceSlope (upperSide w) (incrementFamily r t g v w)-
      (∑ k, (nodeSign k.val v : ℝ)*(F k).field (foldedAngle w))-
      orderedDirection (fun k => pathGap r (g k)*|(correctionPath r t w).im|) v|≤slopeError g F w := by
  let b (k : Fin K) := faceSlope (upperSide w) (correctedPhase r t 1 (g k) w)
  let f (k : Fin K) := (F k).field (foldedAngle w)
  let q (k : Fin K) := pathGap r (g k)*|(correctionPath r t w).im|
  have he : (∑ k, (nodeSign k.val v : ℝ)*b k)-(∑ k, (nodeSign k.val v : ℝ)*f k)-
      orderedDirection q v=∑ k, (nodeSign k.val v : ℝ)*(b k-f k-q k) := by
    simp only [orderedDirection,← nodeSign_mul,mul_sub,sum_sub_distrib]
  rw [incrementFamily,faceSlope_sum]
  change |(∑ k, (nodeSign k.val v : ℝ)*b k)-(∑ k, (nodeSign k.val v : ℝ)*f k)-orderedDirection q v|≤_
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro k _
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (nodeSign_abs _ _)).trans_eq
    (unit_increment_error hr ht ht1 (g k) (hg k) (F k).field w hw hi)

theorem slopeError_integrable {K : ℕ} {z : ℚ} (hz : ‖((z : ℝ) : ℂ)‖<1) (g : Fin K → ℂ[X]) (F : Fin K → ArcForm) :
    Integrable (slopeError g F) (poissonLaw z) := by
  apply integrable_finsetSum
  intro k _
  exact ((integrable_on_poisson_circle hz (by fun_prop : ContinuousOn (fun w : ℂ => ((g k).eval w).im) (sphere 0 1))).sub
    (signedFold_integrable hz (F k).field_measurable (fun θ _ => (F k).field_abs θ))).abs

theorem slopeError_integral {K : ℕ} {z : ℚ} (hz : ‖((z : ℝ) : ℂ)‖<1) (g : Fin K → ℂ[X]) (F : Fin K → ArcForm)
    (ε : ℝ) (he : ∀ k, (∫ w, |((g k).eval w).im-signedFold (F k).field w| ∂poissonLaw z)≤ε) :
    (∫ w, slopeError g F w ∂poissonLaw z)≤(K : ℝ)*ε := by
  unfold slopeError
  rw [integral_finsetSum]
  · simpa using sum_le_sum (s := univ) (fun k _ => he k)
  · intro k _
    exact ((integrable_on_poisson_circle hz (by fun_prop : ContinuousOn (fun w : ℂ => ((g k).eval w).im) (sphere 0 1))).sub
      (signedFold_integrable hz (F k).field_measurable (fun θ _ => (F k).field_abs θ))).abs

theorem imaginary_nonzero_ae {r : ℝ} (hr : 0<r) (hr1 : r<1) : ∀ᵐ w ∂poissonLaw r, w.im≠0 := by
  filter_upwards [foldedAngle_positive_ae hr hr1] with w hw
  intro he
  simp [foldedAngle,he] at hw

end PiPolynomialValues
