module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Every continuous real boundary majorant is uniformly approximable
by the real part of a single analytic polynomial on the unit circle. -/

@[expose] public section

namespace PiPolynomialValues

open AddCircle Polynomial Complex Finset
open scoped ComplexConjugate

noncomputable def boundaryMonomial (k : ℤ) (a : ℂ) : ℂ[X] := match k with
  | .ofNat n => C a*X^n
  | .negSucc n => C (conj a)*X^(n+1)

theorem boundaryMonomial_re (k : ℤ) (a : ℂ) (z : Circle) :
    ((boundaryMonomial k a).eval (z : ℂ)).re = (a*(z : ℂ)^k).re := by
  cases k with
  | ofNat n => simp [boundaryMonomial]
  | negSucc n =>
    have h : ((z : ℂ)^(n+1))⁻¹ = conj ((z : ℂ)^(n+1)) := by
      simpa only [Circle.coe_pow,Circle.coe_inv] using Circle.coe_inv_eq_conj (z^(n+1))
    simp only [boundaryMonomial,eval_mul,eval_C,eval_pow,eval_X,zpow_negSucc,h]
    rw [← Complex.conj_re (a * conj ((z : ℂ)^(n+1))),map_mul]
    simp

theorem exists_polynomial_re_approx (b : C(Circle,ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z : Circle, |(p.eval (z : ℂ)).re-b z| < ε := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  let g : C(AddCircle (1 : ℝ),ℂ) :=
    ⟨fun t => (b (e t) : ℂ),Complex.continuous_ofReal.comp (b.continuous.comp e.continuous)⟩
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let S := Submodule.span ℂ (Set.range (@fourier (1 : ℝ)))
  have hg : g ∈ closure (S : Set C(AddCircle (1 : ℝ),ℂ)) := by
    rw [← Submodule.topologicalClosure_coe,show S.topologicalClosure=⊤ from span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨v,hv,hεv⟩ := Metric.mem_closure_iff.mp hg ε hε
  obtain ⟨l,hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (show v ∈ S from hv)
  let p : ℂ[X] := l.sum boundaryMonomial
  refine ⟨p,fun z => ?_⟩
  let t := e.symm z
  have hz : e t=z := e.apply_symm_apply z
  have hfourier (k : ℤ) : fourier k t = (z : ℂ)^k := by
    rw [fourier_apply,AddCircle.toCircle_zsmul,Circle.coe_zpow]
    have he : AddCircle.toCircle t=z := (AddCircle.homeomorphCircle_apply one_ne_zero t).symm.trans hz
    rw [he]
  have hp : (p.eval (z : ℂ)).re = (v t).re := by
    rw [← hl]
    simp only [p,Finsupp.sum,eval_finsetSum,Complex.re_sum,ContinuousMap.sum_apply,
      ContinuousMap.smul_apply,smul_eq_mul,hfourier,boundaryMonomial_re]
  have hvz : ‖g t-v t‖ < ε := by
    apply lt_of_le_of_lt ((g-v).norm_coe_le_norm t)
    simpa only [dist_eq_norm] using hεv
  have hreal := (Complex.abs_re_le_norm (g t-v t)).trans_lt hvz
  rw [hp,abs_sub_comm]
  simpa [g,hz,Complex.sub_re] using hreal

end PiPolynomialValues
