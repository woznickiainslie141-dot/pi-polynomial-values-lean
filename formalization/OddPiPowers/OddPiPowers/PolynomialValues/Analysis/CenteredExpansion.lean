module

public import OddPiPowers.PolynomialValues.Analysis.TriangularColumnShift

/-! Exact translated column terms. At a positive label the boundary
column vanishes on its center node, while its origin expansion only
uses powers of the node indexed at most by that label. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

noncomputable def centeredLabelMatrix {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ) : Matrix (Fin n) (Fin n) ℂ := pathMatrix e x (fun l => j l-(h l).val)
    (fun i _ => p i) (fun i l => (2 : ℂ)^(j l)*((v i : ℂ)-(a (x l) : ℂ))^(h l).val*
      Complex.exp ((x l : ℂ)*p i))

theorem centeredLabelMatrix_zero {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ) (i l : Fin n) (he : v (e i).1 = a (x l)) (hh : (h l).val ≠ 0) :
    centeredLabelMatrix e v x j a h p i l = 0 := by
  simp [centeredLabelMatrix,pathMatrix,he,hh]

theorem normalized_det_centered {n V J : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    {U : Fin J → ℕ} (hU : Antitone U) (d : Fin n ≃ Column U) (v : Fin V → ℤ)
    (y : ℂ) (a : ℤ → ℤ) :
    let x (l : Fin n) := (d l).2.val
    let j (l : Fin n) := (d l).1.val
    let δ := Complex.I*(y-(Real.pi : ℂ))/2
    (Matrix.of (fun i l => normalizedEntry (v (e i).1) (x l) (e i).2.val (j l) y)).det =
      ∑ h : LabelChoice j, labelCoefficient j h δ*
        (centeredLabelMatrix e v x j a h (fun i => phasePoint (v i))).det := by
  intro x j δ
  let w (t : ℤ) := -(a t : ℂ)*δ
  let c (l : Fin n) (k : Fin (j l+1)) := ((j l).choose k.val : ℂ)*δ^k.val
  let f (l : Fin n) (k : Fin (j l+1)) (i : Fin n) :=
    let u := v (e i).1
    (2 : ℂ)^(j l)*((u : ℂ)-(a (x l) : ℂ))^k.val*Complex.exp ((x l : ℂ)*phasePoint u)*
      (rowOperator 1 (phasePoint u) (j l-k.val) (normalizedRowPolynomial (e i).2.val)).eval (x l : ℂ)
  rw [← det_shiftedEntry hU d (fun i => v (e i).1) (fun i => (e i).2.val) y w]
  have he : Matrix.of (fun i l => shiftedEntry (v (e i).1) (x l) (e i).2.val (j l) y (w (x l))) =
      Matrix.of (fun i l => ∑ k, c l k*f l k i) := by
    ext i l
    let u := v (e i).1
    have hu : (u : ℂ)*Complex.I*y/2+w (x l) = phasePoint u + ((u : ℂ)-(a (x l) : ℂ))*δ := by
      unfold phasePoint w δ
      ring
    change (2 : ℂ)^j l*Complex.I^(u*x l)*
      (rowOperator 1 ((u : ℂ)*Complex.I*y/2+w (x l)) (j l) (normalizedRowPolynomial (e i).2.val)).eval (x l : ℂ) = _
    rw [hu,rowOperator_perturb,eval_finsetSum,mul_sum,Matrix.of_apply,← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro k _
    simp only [c,f,phasePoint_exp,eval_mul,eval_C,mul_pow,u]
    ring
  rw [he,det_weighted_columns]
  rfl

noncomputable def nodePowerMatrix {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j l q : Fin n → ℕ) (p : Fin V → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := pathMatrix e x (fun c => j c-l c) (fun i _ => p i)
    (fun i c => (2 : ℂ)^(j c)*(v i : ℂ)^(q c)*Complex.exp ((x c : ℂ)*p i))

theorem centered_det_node_powers {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ) :
    let l (c : Fin n) := (h c).val
    (centeredLabelMatrix e v x j a h p).det =
      ∑ q : LabelChoice l, (∏ c, ((l c).choose (q c).val : ℂ)*(-(a (x c) : ℂ))^(l c-(q c).val))*
        (nodePowerMatrix e v x j l (fun c => (q c).val) p).det := by
  intro l
  let b (c : Fin n) (k : Fin (l c+1)) := ((l c).choose k.val : ℂ)*(-(a (x c) : ℂ))^(l c-k.val)
  let f (c : Fin n) (k : Fin (l c+1)) (i : Fin n) := (2 : ℂ)^j c*(v (e i).1 : ℂ)^k.val*
    Complex.exp ((x c : ℂ)*p (e i).1)*
    (rowOperator 1 (p (e i).1) (j c-l c) (normalizedRowPolynomial (e i).2.val)).eval (x c : ℂ)
  have he : centeredLabelMatrix e v x j a h p = Matrix.of (fun i c => ∑ k, b c k*f c k i) := by
    ext i c
    change (2 : ℂ)^j c*((v (e i).1 : ℂ)-(a (x c) : ℂ))^(l c)*_*_ = _
    rw [sub_eq_add_neg,add_pow,← Fin.sum_univ_eq_sum_range,mul_sum,sum_mul,sum_mul,Matrix.of_apply]
    apply sum_congr rfl
    intro k _
    dsimp only [b,f]
    ring
  rw [he,det_weighted_columns]
  rfl

end PiPolynomialValues.FourPeriod
