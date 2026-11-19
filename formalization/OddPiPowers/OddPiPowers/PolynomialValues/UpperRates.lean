module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! Eventual one-sided bounds for signed logarithmic rates. A rate can
be arbitrarily negative along a subsequence. -/

@[expose] public section

namespace PiPolynomialValues

open Filter Finset
open scoped Topology

def UpperRate {ι : Type*} (F : Filter ι) (f : ι → ℝ) (a : ℝ) : Prop :=
  ∀ ε>0, ∀ᶠ i in F, f i≤a+ε

namespace UpperRate

variable {ι κ : Type*} {F : Filter ι} {G : Filter κ} {f g : ι → ℝ} {a b : ℝ}

theorem of_tendsto (h : Tendsto f F (𝓝 a)) : UpperRate F f a := by
  intro ε hε
  exact (h.eventually (gt_mem_nhds (show a<a+ε by linarith))).mono (fun _ hh => hh.le)

theorem of_eventually (h : ∀ᶠ i in F, f i≤a) : UpperRate F f a := fun _ hε =>
  h.mono (fun _ hh => hh.trans (le_add_of_nonneg_right hε.le))

theorem mono (h : UpperRate F g a) (hle : ∀ᶠ i in F, f i≤g i) (hab : a≤b) : UpperRate F f b := by
  intro ε hε
  filter_upwards [h ε hε,hle] with i hi hf
  exact hf.trans (hi.trans (add_le_add hab le_rfl))

theorem comp (h : UpperRate F f a) {φ : κ → ι} (hφ : Tendsto φ G F) :
    UpperRate G (fun k => f (φ k)) a := fun ε hε => hφ.eventually (h ε hε)

theorem add (hf : UpperRate F f a) (hg : UpperRate F g b) : UpperRate F (fun i => f i+g i) (a+b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (half_pos hε),hg (ε/2) (half_pos hε)] with i h₁ h₂
  linarith only [h₁,h₂]

theorem sum {I : Type*} (s : Finset I) (u : I → ι → ℝ) (v : I → ℝ)
    (h : ∀ j∈s, UpperRate F (u j) (v j)) : UpperRate F (fun i => ∑ j∈s, u j i) (∑ j∈s, v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (of_tendsto (tendsto_const_nhds (f := F) (x := (0 : ℝ))))
  | insert j s hj ih =>
    have H := (h j (mem_insert_self _ _)).add (ih (fun k hk => h k (mem_insert_of_mem hk)))
    simpa [sum_insert,hj] using H

theorem mul_scale (hf : UpperRate F f a) {u : ι → ℝ} {L : ℝ} (hu : Tendsto u F (𝓝 L))
    (hpos : ∀ᶠ i in F, 0≤u i) (hL : 0≤L) : UpperRate F (fun i => u i*f i) (L*a) := by
  intro ε hε
  let δ := ε/(2*(L+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hB : L*(a+δ)<L*a+ε := by
    have he : 2*(L+1)*δ=ε := by dsimp [δ]; field_simp
    nlinarith only [he,hδ,hε,mul_nonneg hL hδ.le]
  filter_upwards [hf δ hδ,hpos,(hu.mul_const (a+δ)).eventually (gt_mem_nhds hB)] with i hi hp h
  exact (mul_le_mul_of_nonneg_left hi hp).trans h.le

theorem nonneg_limit [F.NeBot] (h : UpperRate F f a) (hf : ∀ᶠ i in F, 0≤f i) : 0≤a := by
  by_contra! ha
  obtain ⟨i,hi,hj⟩ := ((h (-a/2) (by linarith)).and hf).exists
  linarith

end UpperRate
end PiPolynomialValues
