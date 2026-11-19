module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxFloor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! Endpoint comparisons imply disjointness throughout the whole slab,
including strips that meet or collapse at an endpoint. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

private def boundaryDifference (f g : Boundary) : Boundary := ⟨g.slope-f.slope,g.offset-f.offset⟩

private theorem difference_value (f g : Boundary) (t : ℝ) :
    (boundaryDifference f g).value t = g.value t - f.value t := by
  simp only [Boundary.value, boundaryDifference, Int.cast_sub]
  ring

private theorem order_at_endpoint (f g : Boundary) (e : Abscissa) (he : 0 < e.den)
    (h : f.ordinate e ≤ g.ordinate e) : f.value e.value ≤ g.value e.value := by
  rw [affine_numerator f e he, affine_numerator g e he]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem boundary_order_inside (f g : Boundary) (l r : Abscissa) (hl : 0 < l.den) (hr : 0 < r.den)
    {t : ℝ} (hlt : l.value ≤ t) (htr : t ≤ r.value) (h₁ : f.ordinate l ≤ g.ordinate l)
    (h₂ : f.ordinate r ≤ g.ordinate r) : f.value t ≤ g.value t := by
  have hp (e : Abscissa) (he : 0 < e.den) (h : f.ordinate e ≤ g.ordinate e) :
      0 ≤ (boundaryDifference f g).value e.value := by
    rw [difference_value]
    exact sub_nonneg.mpr (order_at_endpoint f g e he h)
  have hout : 0 ≤ (boundaryDifference f g).value t := by
    rcases (boundaryDifference f g).monotone_or_antitone with m | a
    · exact (hp l hl h₁).trans (m hlt)
    · exact (hp r hr h₂).trans (a htr)
  rw [difference_value] at hout
  exact sub_nonneg.mp hout

def stripOrder (t : ℝ) (prev : Boundary) : List Box → Prop
  | [] => True
  | b :: bs => prev.value t ≤ b.bottom.value t ∧ b.bottom.value t ≤ b.top.value t ∧
      b.top.value t ≤ 1/2 ∧ stripOrder t b.top bs

theorem checked_strips (s : Shape) (l r : Abscissa) (hl : 0 < l.den) (hr : 0 < r.den)
    {t : ℝ} (hlt : l.value ≤ t) (htr : t ≤ r.value) (prev : Boundary) (bs : List Box)
    (hs : boxesPass s l r prev bs = true) :
    stripOrder t prev bs ∧ ∀ b ∈ bs, dualPass s l r b = true ∧ areaPass s l r b = true := by
  induction bs generalizing prev with
  | nil => simp [stripOrder]
  | cons b bs ih =>
    simp only [boxesPass, Bool.and_eq_true] at hs
    have h₁ : linesPass l prev b = true := by tauto
    have h₂ : linesPass r prev b = true := by tauto
    have hd : dualPass s l r b = true := by tauto
    have ha : areaPass s l r b = true := by tauto
    have hrest : boxesPass s l r b.top bs = true := by tauto
    have a := of_decide_eq_true h₁
    have c := of_decide_eq_true h₂
    have hhalf := boundary_order_inside b.top (⟨0,1⟩ : Boundary) l r hl hr hlt htr
      (by simpa [Boundary.ordinate] using a.2.2) (by simpa [Boundary.ordinate] using c.2.2)
    obtain ⟨ord, rest⟩ := ih b.top hrest
    refine ⟨⟨boundary_order_inside _ _ l r hl hr hlt htr a.1 c.1,
      boundary_order_inside _ _ l r hl hr hlt htr a.2.1 c.2.1, ?_, ord⟩, ?_⟩
    · simpa [Boundary.value] using hhalf
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | h
      · exact ⟨hd,ha⟩
      · exact rest z h

end PiPolynomialValues.PrimeWindow
