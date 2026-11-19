module

public import OddPiPowers.PolynomialValues.Analysis.NormalizedBlockBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The perturbation at a complex conjugate expands the actual normalized
minor into independently labelled columns of the same path determinant. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

noncomputable def phasePoint (v : ℤ) : ℂ := (v : ℂ)*Complex.I*(Real.pi : ℂ)/2

theorem phasePoint_exp (t v : ℤ) :
    Complex.exp ((t : ℂ)*phasePoint v) = Complex.I^(v*t) := by
  have h : (t : ℂ)*phasePoint v = ((v*t : ℤ) : ℂ)*((Real.pi : ℂ)/2*Complex.I) := by
    rw [Int.cast_mul]
    unfold phasePoint
    ring
  rw [h,Complex.exp_int_mul,Complex.exp_pi_div_two_mul_I]

theorem det_weighted_columns {n : ℕ} {ι : Fin n → Type*} [∀ j, Fintype (ι j)]
    (a : ∀ j, ι j → ℂ) (f : ∀ j, ι j → Fin n → ℂ) :
    (Matrix.of (fun i j => ∑ k, a j k*f j k i)).det =
      ∑ h : (∀ j, ι j), (∏ j, a j (h j))*(Matrix.of fun i j => f j (h j) i).det := by
  classical
  let L := (Matrix.detRowAlternating (n := Fin n) (R := ℂ)).toMultilinearMap
  let A := Matrix.of (fun i j => ∑ k, a j k*f j k i)
  have he : A.transpose.det = L (fun j => ∑ k, a j k • f j k) := by
    apply congrArg Matrix.det
    ext i j
    simp [A,Pi.smul_apply]
  change A.det = _
  rw [← Matrix.det_transpose A,he,L.map_sum]
  apply sum_congr rfl
  intro h _
  rw [L.map_smul_univ,smul_eq_mul]
  congr 1
  change (Matrix.of fun j i => f j (h j) i).det = _
  rw [← Matrix.det_transpose]
  rfl

abbrev LabelChoice {n : ℕ} (j : Fin n → ℕ) := (l : Fin n) → Fin (j l+1)

noncomputable def labelledMatrix {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (h : LabelChoice j)
    (p : Fin V → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  pathMatrix e x (fun l => j l-(h l).val) (fun i _ => p i)
    (fun i l => (2 : ℂ)^(j l)*(v i : ℂ)^(h l).val*Complex.exp ((x l : ℂ)*p i))

noncomputable def labelCoefficient {n : ℕ} (j : Fin n → ℕ) (h : LabelChoice j) (δ : ℂ) : ℂ :=
  ∏ l, ((j l).choose (h l).val : ℂ)*δ^(h l).val

theorem normalized_det_perturbation {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (y : ℂ) :
    (Matrix.of (fun i l => normalizedEntry (v (e i).1) (x l) (e i).2.val (j l) y)).det =
      ∑ h : LabelChoice j, labelCoefficient j h (Complex.I*(y-(Real.pi : ℂ))/2)*
        (labelledMatrix e v x j h (fun i => phasePoint (v i))).det := by
  let δ := Complex.I*(y-(Real.pi : ℂ))/2
  let a (l : Fin n) (k : Fin (j l+1)) := ((j l).choose k.val : ℂ)*δ^k.val
  let f (l : Fin n) (k : Fin (j l+1)) (i : Fin n) :=
    let u := v (e i).1
    (2 : ℂ)^(j l)*(u : ℂ)^k.val*Complex.exp ((x l : ℂ)*phasePoint u)*
      (rowOperator 1 (phasePoint u) (j l-k.val) (normalizedRowPolynomial (e i).2.val)).eval (x l : ℂ)
  have he : Matrix.of (fun i l => normalizedEntry (v (e i).1) (x l) (e i).2.val (j l) y) =
      Matrix.of (fun i l => ∑ k, a l k*f l k i) := by
    ext i l
    let u := v (e i).1
    have hu : (u : ℂ)*Complex.I*y/2 = phasePoint u + (u : ℂ)*δ := by
      unfold phasePoint δ
      ring
    change (2 : ℂ)^j l*Complex.I^(u*x l)*
      (rowOperator 1 ((u : ℂ)*Complex.I*y/2) (j l) (normalizedRowPolynomial (e i).2.val)).eval (x l : ℂ) = _
    rw [hu,rowOperator_perturb,eval_finsetSum,mul_sum,Matrix.of_apply,← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro k _
    simp only [a,f,phasePoint_exp,eval_mul,eval_C,mul_pow,u]
    ring
  rw [he,det_weighted_columns]
  rfl

end PiPolynomialValues.FourPeriod
