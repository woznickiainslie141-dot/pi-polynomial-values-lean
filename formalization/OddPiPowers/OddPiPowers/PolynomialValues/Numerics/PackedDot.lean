module

public import OddPiPowers.PolynomialValues.Numerics.PackedWindows

/-! The middle coefficient of a product with a reversed weight row
is the exact scalar product, including when the field has both signs. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Polynomial

def packedDot (b bias : ℤ) (n : ℕ) (values reversedWeights : ℤ) :=
  packedDigit b (values*reversedWeights+bias*packedOnes b (n+n)) (n-1)-bias

theorem packedDot_sound {b bias M S : ℤ} {n : ℕ} (hb : 1<b) (hn : 0<n)
    (v w : ℕ → ℤ) (hM : 0≤M) (hw : ∀ j<n, |w j|≤M) (hv : ∑ j ∈ range n, |v j|≤S)
    (hlo : M*S≤bias) (hhi : M*S+bias<b) :
    packedDot b bias n (packedSum b n v) (packEval b n (fun j => w (n-1-j))) =
      ∑ j ∈ range n, w j*v j := by
  let a (j : ℕ) := w (n-1-j)
  have hA (j : ℕ) (hj : j<n) : |a j|≤M := hw _ (by omega)
  let P := coefficientPoly n a
  let Q := coefficientPoly n v
  have hdeg : P.natDegree+Q.natDegree<n+n := by
    have hp := coefficientPoly_degree hn a
    have hq := coefficientPoly_degree hn v
    dsimp [P,Q]
    omega
  have hr (i : ℕ) (_ : i<n+n) : 0≤(P*Q).coeff i+bias ∧ (P*Q).coeff i+bias<b := by
    have H := abs_le.mp ((meshConvolution_abs hM hA (c := v) i).trans (mul_le_mul_of_nonneg_left hv hM))
    rw [show (P*Q).coeff i=meshConvolution n n a v i from meshConvolution_coeff _ _ _ _ _]
    constructor <;> omega
  have H := convolution_digit P Q (show 0<b by omega) (n+n) hdeg bias hr (k := n-1) (by omega)
  simp only [P,Q,meshConvolution_coeff,coefficientPoly_eval] at H
  rw [packedDot,packEval_eq,packedOnes_eq hb,mul_comm (packedSum b n v),H,
    meshConvolution_interior (by omega) (by omega : n-1<n)]
  apply sum_congr rfl
  intro j hj
  have he : n-1-(n-1-j)=j := by have := mem_range.mp hj; omega
  simp [a,he]

end PiPolynomialValues
