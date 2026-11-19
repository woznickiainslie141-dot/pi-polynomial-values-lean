module

public import OddPiPowers.PolynomialValues.Numerics.SlabEligibility
public import OddPiPowers.PolynomialValues.Numerics.PrimeTailSound

/-! Lower limits of the actual weighted lattice counts. Shrinking each
side of a fixed slab changes its total integrated affine width continuously. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod Finset Filter MeasureTheory
open scoped Topology Interval

def LowerRate (f : ℕ → ℝ) (x : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, x-ε ≤ f n

theorem LowerRate.add {f g : ℕ → ℝ} {x y : ℝ} (hf : LowerRate f x) (hg : LowerRate g y) :
    LowerRate (fun n => f n+g n) (x+y) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity)] with n h₁ h₂
  linarith

theorem LowerRate.scale {f : ℕ → ℝ} {x : ℝ} (h : LowerRate f x) {a : ℝ} (ha : 0 ≤ a) :
    LowerRate (fun n => a*f n) (a*x) := by
  intro ε hε
  have hz : 0 < a+1 := by linarith
  have hdiv : a*(ε/(a+1)) ≤ ε := by
    rw [← mul_div_assoc,div_le_iff₀ hz]
    nlinarith only [hε]
  filter_upwards [h (ε/(a+1)) (div_pos hε hz)] with n hn
  linarith only [mul_le_mul_of_nonneg_left hn ha,hdiv]

theorem LowerRate.mono {f g : ℕ → ℝ} {x : ℝ} (h : LowerRate f x) (he : ∀ᶠ n in atTop, f n ≤ g n) :
    LowerRate g x := by
  intro ε hε
  filter_upwards [h ε hε,he] with n hh hfg
  exact hh.trans hfg

theorem LowerRate.comp {f : ℕ → ℝ} {x : ℝ} (h : LowerRate f x) {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop) : LowerRate (fun n => f (s n)) x := fun ε hε => hs.eventually (h ε hε)

noncomputable def stripAreaSum (bs : List Box) (l r : ℝ) : ℝ :=
  (bs.map (fun b => (2*b.gain : ℝ)*(∫ y in r⁻¹..l⁻¹, stripWidth b y))).sum

noncomputable def windowLatticeRate (W : OddPiPowers.PrimeRates.PrimeWindow) (bs : List Box) (N : ℕ) : ℝ :=
  (∑ p ∈ W.primes N, (latticeSaving bs N p : ℝ)*Real.log p)/(N : ℝ)^2

theorem window_lattice_rate (W : OddPiPowers.PrimeRates.PrimeWindow) (bs : List Box) :
    LowerRate (windowLatticeRate W bs) (stripAreaSum bs W.lower W.upper) := by
  induction bs with
  | nil =>
    intro ε hε
    exact Eventually.of_forall (fun n => by simp [windowLatticeRate,latticeSaving,stripAreaSum,hε.le])
  | cons b bs ih =>
    let G := (2*b.gain : ℝ)
    have hb : LowerRate (fun N : ℕ => (∑ p ∈ W.primes N, ((residuePoints b N p).card : ℝ)*Real.log p)/(N : ℝ)^2)
        (∫ y in W.upper⁻¹..W.lower⁻¹, stripWidth b y) := fun _ hε => residue_prime_sum_eventually W b hε
    have hh := (hb.scale (a := G) (by dsimp [G]; positivity)).add ih
    apply hh.mono
    apply Eventually.of_forall
    intro N
    unfold windowLatticeRate
    have he (p : ℕ) : (latticeSaving (b::bs) N p : ℝ) =
        G*((residuePoints b N p).card : ℝ)+(latticeSaving bs N p : ℝ) := by
      simp [latticeSaving,G]
    simp only [he,add_mul,Finset.sum_add_distrib,mul_assoc,← mul_sum]
    exact le_of_eq (by ring)

theorem stripAreaSum_continuous_at (bs : List Box) {l r : ℝ} (hl : l ≠ 0) (hr : r ≠ 0) :
    ContinuousAt (fun δ : ℝ => stripAreaSum bs (l+δ) (r-δ)) 0 := by
  induction bs with
  | nil => exact continuousAt_const
  | cons b bs ih =>
    apply ContinuousAt.add _ ih
    simp only [stripWidth,integral_affine_real]
    fun_prop (disch := simp [hl,hr])

theorem exists_trimmed_window (bs : List Box) {l r ε : ℝ} (hl : 0 < l) (hlr : l < r) (hε : 0 < ε) :
    ∃ (δ : ℝ) (W : OddPiPowers.PrimeRates.PrimeWindow), 0 < δ ∧ W.lower = l+δ ∧ W.upper = r-δ ∧
      stripAreaSum bs l r-ε ≤ stripAreaSum bs W.lower W.upper := by
  have hc := stripAreaSum_continuous_at bs hl.ne' (hl.trans hlr).ne'
  obtain ⟨q,hq,hcl⟩ := Metric.continuousAt_iff.mp hc ε hε
  let δ := min (q/2) ((r-l)/4)
  have hd : 0 < δ := lt_min (by positivity) (by linarith)
  have hdq : δ < q := (min_le_left _ _).trans_lt (by linarith)
  have hdr : δ ≤ (r-l)/4 := min_le_right _ _
  have hW : l+δ < r-δ := by linarith
  let W : OddPiPowers.PrimeRates.PrimeWindow := ⟨l+δ,r-δ,0,add_pos hl hd,hW⟩
  refine ⟨δ,W,hd,rfl,rfl,?_⟩
  have h := hcl (x := δ) (by simpa [Real.dist_eq,abs_of_pos hd] using hdq)
  simp only [Real.dist_eq,add_zero,sub_zero,abs_lt] at h
  change stripAreaSum bs l r-ε ≤ stripAreaSum bs (l+δ) (r-δ)
  linarith only [h.1]

end PiPolynomialValues.PrimeWindow
