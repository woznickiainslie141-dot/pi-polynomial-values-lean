module

public import OddPiPowers.PolynomialValues.Analysis.CircleApproximation

/-! The imaginary part of a polynomial real on the real axis uniformly
approximates the odd part of a continuous field on the unit circle. -/

@[expose] public section

namespace PiPolynomialValues

open Complex Polynomial
open scoped ComplexConjugate

theorem conjugate_polynomial_eval (p : ℂ[X]) (z : ℂ) :
    (p.map (starRingEnd ℂ)).eval z=conj (p.eval (conj z)) := by
  simpa using (Polynomial.eval_map_apply (p := p) (f := starRingEnd ℂ) (conj z))

theorem exists_real_path_oddpart (b : C(Circle,ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∃ g : ℂ[X], g.eval 0=0 ∧ (∀ x : ℝ, (g.eval (x : ℂ)).im=0) ∧
      ∀ z : Circle, |(g.eval (z : ℂ)).im-(b z-b z⁻¹)/2|<ε := by
  obtain ⟨p,hp⟩ := exists_polynomial_re_approx b hε
  let q := C (Complex.I/2)*(p-p.map (starRingEnd ℂ))
  have he (z : ℂ) : (q.eval z).im=((p.eval z).re-(p.eval (conj z)).re)/2 := by
    simp [q,conjugate_polynomial_eval,Complex.mul_im,Complex.sub_re]
    <;> ring
  let g := q-C (q.eval 0)
  have hg (z : ℂ) : (g.eval z).im=((p.eval z).re-(p.eval (conj z)).re)/2 := by
    simp [g,Complex.sub_im,he]
  refine ⟨g,by simp [g],fun x => by simp [hg],?_⟩
  intro z
  have h1 := abs_lt.mp (hp z)
  have h2 := abs_lt.mp (hp z⁻¹)
  rw [Circle.coe_inv_eq_conj] at h2
  rw [hg,abs_lt]
  constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2]

end PiPolynomialValues
