module

public import OddPiPowers.PolynomialValues.Analysis.OriginFunctions
public import OddPiPowers.PolynomialValues.Analysis.LabelOrderDeterminant
public import OddPiPowers.PolynomialValues.Analysis.CenteredExpansion

/-! Analytic divisibility of each node-power determinant for genuinely
independent paths at the different nodes. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

theorem dividedRow_det_dvd {n : ℕ} (p : Fin n → OriginFunction) (hp : ∀ i, (p i).val 0=0)
    (f : Fin n → ℂ → ℂ) (hf : ∀ j, AnalyticAt ℂ (f j) 0) (u : Fin n → ℂ)
    (q σ : Fin n → ℕ) (b : Fin n → ℂ) :
    originCoordinate^(labelPairs q-∑ i, σ i) ∣ (Matrix.of (fun i j =>
      originConst (b j*(u i)^q j)*pathTaylorRow (f j) (hf j) (p i) (hp i) (σ i))).det := by
  let H := labelPairs q-∑ i, σ i
  let S := univ.sup σ
  let K := S+H
  let a (j : Fin n) (k : Fin K) := originConst (b j*iteratedDeriv k.val (f j) 0)
  let D (l : ℕ) (k : Fin K) (i : Fin n) :=
    originConst ((u i)^l)*(originConst (jetCoefficient (σ i) k.val)*(p i)^(k.val-σ i))
  let B := Matrix.of (fun i j => ∑ k : Fin K, a j k*D (q j) k i)
  apply det_dvd_of_entry_congr _ _ B
  · intro i j
    have hh : σ i + H ≤ K := Nat.add_le_add_right (le_sup (f := σ) (mem_univ i)) _
    have ht := dvd_mul_of_dvd_right (pathTaylorRow_truncation (f j) (hf j) (p i) (hp i) (σ i) H K hh)
      (originConst (b j*(u i)^q j))
    rw [mul_sub,mul_sum] at ht
    obtain ⟨g,hg⟩ := ht
    refine ⟨g,?_⟩
    rw [← hg]
    symm
    change _ - _ = _ - (∑ k : Fin K, a j k*D (q j) k i)
    congr 1
    apply sum_congr rfl
    intro k _
    apply Subtype.ext
    funext z
    change (b j*(u i)^q j)*(iteratedDeriv k.val (f j) 0*(jetCoefficient (σ i) k.val*(p i).val z^(k.val-σ i))) =
      (b j*iteratedDeriv k.val (f j) 0)*((u i)^q j*(jetCoefficient (σ i) k.val*(p i).val z^(k.val-σ i)))
    ring
  · apply labelled_truncation_dvd originCoordinate q σ a D
    intro l k i
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
      (pow_dvd_pow_of_dvd (originCoordinate_dvd (p i) (hp i)) _) _) _

theorem nodePowerMatrix_factor {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j l q : Fin n → ℕ) (p : Fin V → ℂ → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (p i) 0) (h0 : ∀ i, p i 0=0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∀ z, (nodePowerMatrix e v x j l q (fun i => p i z)).det =
      z^(labelPairs q-∑ i, (e i).2.val)*G z := by
  let P (i : Fin n) : OriginFunction := ⟨p (e i).1,ha _⟩
  let f (c : Fin n) := columnFunction (x c : ℂ) (j c-l c)
  have hf (c : Fin n) : AnalyticAt ℂ (f c) 0 := by
    unfold f columnFunction
    fun_prop
  obtain ⟨g,hg⟩ := dividedRow_det_dvd P (fun _ => h0 _) f hf (fun i => (v (e i).1 : ℂ))
    q (fun i => (e i).2.val) (fun c => (2 : ℂ)^j c)
  refine ⟨g.val,g.property,fun z => ?_⟩
  have h := congrArg (originEval z) hg
  rw [(originEval z).map_det,map_mul,map_pow] at h
  apply Eq.trans _ h
  apply congrArg Matrix.det
  ext i c
  change (2 : ℂ)^j c*(v (e i).1 : ℂ)^q c*Complex.exp ((x c : ℂ)*p (e i).1 z)*
    (rowOperator 1 (p (e i).1 z) (j c-l c) (normalizedRowPolynomial (e i).2.val)).eval (x c : ℂ) =
    (2^j c*(v (e i).1 : ℂ)^q c)*dividedRow (e i).2.val (columnFunction (x c) (j c-l c)) (p (e i).1 z)
  rw [dividedRow_columnFunction]
  ring

theorem centeredLabelMatrix_factor {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ → ℂ) (ha : ∀ i, AnalyticAt ℂ (p i) 0) (h0 : ∀ i, p i 0=0) :
    ∃ q : LabelChoice (fun c => (h c).val), ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∀ z,
      (centeredLabelMatrix e v x j a h (fun i => p i z)).det =
        z^(labelPairs (fun c => (q c).val)-∑ i, (e i).2.val)*G z := by
  classical
  let l (c : Fin n) := (h c).val
  let H (q : LabelChoice l) := labelPairs (fun c => (q c).val)-∑ i, (e i).2.val
  let b (q : LabelChoice l) := ∏ c, ((l c).choose (q c).val : ℂ)*(-(a (x c) : ℂ))^(l c-(q c).val)
  obtain ⟨s,_,hs⟩ := univ.exists_min_image H univ_nonempty
  choose g hg he using fun q : LabelChoice l =>
    nodePowerMatrix_factor e v x j l (fun c => (q c).val) p ha h0
  refine ⟨s,fun z => ∑ q, b q*(z^(H q-H s)*g q z),?_,?_⟩
  · apply Finset.analyticAt_fun_sum
    intro q _
    exact analyticAt_const.mul ((analyticAt_id.pow _).mul (hg q))
  · intro z
    rw [centered_det_node_powers,mul_sum]
    apply sum_congr rfl
    intro q _
    rw [he q]
    have hk : H s+(H q-H s)=H q := Nat.add_sub_of_le (hs q (mem_univ _))
    change b q*(z^H q*g q z) = z^H s*(b q*(z^(H q-H s)*g q z))
    rw [show z^H q=z^H s*z^(H q-H s) from
      (congrArg (fun t : ℕ => z^t) hk.symm).trans (pow_add _ _ _)]
    ring

end PiPolynomialValues.FourPeriod
