module

public import OddPiPowers.PolynomialValues.FourPeriod.ScaledDegree
public import OddPiPowers.PolynomialValues.Numerics.ShapeGeometry

/-! All finite constants apply to the same Gaussian-integer quotient
which is nonzero at the prescribed specialization point. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

theorem quadratic_actual_degree (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    ShapeDegreeWitness quadraticShape quadraticNodeGroups t y 27143631494 4675 := by
  apply shape_degree_witness (w := 586640000) (z := 340837840) (K := 73)
  · exact quadratic_actual_cut_quotient t hy
  · decide
  · rw [quadratic_candidate_excess,shape_column_card]
  · decide +kernel
  · decide +kernel

theorem cubic_actual_degree (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    ShapeDegreeWitness cubicShape cubicNodeGroups t y 141186386926 44847 := by
  apply shape_degree_witness (w := 1041520000) (z := 649387720) (K := 229)
  · exact cubic_actual_cut_quotient t hy
  · decide
  · rw [cubic_candidate_excess,shape_column_card]
  · decide +kernel
  · decide +kernel

theorem quadratic_degree_per_column (t : ℕ) :
    (27143631494 : ℚ)*t + 4675 ≤
      Fintype.card (Column (quadraticShape.band t)) * quadraticRateData.auxDegree + 4675 := by
  rw [shape_column_card]
  change _ ≤ (((8382733616*t+11 : ℕ) : ℚ) * (366805831/113280184)) + 4675
  push_cast
  linarith

theorem cubic_degree_per_column (t : ℕ) :
    (141186386926 : ℚ)*t + 44847 ≤
      Fintype.card (Column (cubicShape.band t)) * cubicRateData.auxDegree + 44847 := by
  rw [shape_column_card]
  change _ ≤ (((25094174576*t+18 : ℕ) : ℚ) * (70593193463/12547087288)) + 44847
  push_cast
  linarith

end PiPolynomialValues.FourPeriod
