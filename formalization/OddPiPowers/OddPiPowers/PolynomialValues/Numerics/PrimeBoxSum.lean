module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxOrder
public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxSound

/-! Sum all selected strips at a point before taking a prime limit. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

noncomputable def stripGains (t τ : ℝ) : List Box → ℤ
  | [] => 0
  | b :: bs =>
      (if b.bottom.value t < τ ∧ τ < b.top.value t then 2*(b.gain : ℤ) else 0) + stripGains t τ bs

private theorem stripGains_below (t τ : ℝ) (prev : Boundary) (bs : List Box)
    (ho : stripOrder t prev bs) (h : τ ≤ prev.value t) : stripGains t τ bs = 0 := by
  induction bs generalizing prev with
  | nil => rfl
  | cons b bs ih =>
    rcases ho with ⟨hp,hb,_,hr⟩
    have hn : ¬(b.bottom.value t < τ ∧ τ < b.top.value t) :=
      fun z => (not_lt_of_ge (h.trans hp)) z.1
    rw [stripGains, if_neg hn, zero_add]
    exact ih b.top hr ((h.trans hp).trans hb)

theorem stripGains_le (t τ : ℝ) (prev : Boundary) (bs : List Box)
    (ho : stripOrder t prev bs) {Z : ℤ} (hZ : 0 ≤ Z)
    (h : ∀ b ∈ bs, b.bottom.value t < τ → τ < b.top.value t → 2*(b.gain : ℤ) ≤ Z) :
    stripGains t τ bs ≤ Z := by
  induction bs generalizing prev with
  | nil => exact hZ
  | cons b bs ih =>
    rcases ho with ⟨_,_,_,hr⟩
    by_cases hit : b.bottom.value t < τ ∧ τ < b.top.value t
    · rw [stripGains, if_pos hit, stripGains_below t τ b.top bs hr hit.2.le, add_zero]
      exact h b (by simp) hit.1 hit.2
    · rw [stripGains, if_neg hit, zero_add]
      exact ih b.top hr (fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem certified_strip_sum (s : Shape) (l r : Abscissa) (prev : Boundary) (bs : List Box)
    (hs : 0 < s.massUnit) (hrows : ∀ i ∈ s.rows, 0 < s.rowUnits i) (hM : 0 < s.rows.length)
    (hl : 0 < l.den) (hr : 0 < r.den) {t τ : ℝ} (hlt : l.value ≤ t) (htr : t < r.value)
    (hb : boxesPass s l r prev bs = true) :
    stripGains t τ bs ≤ collisionTwice (excessAt s t τ) s.rows.length := by
  have h := checked_strips s l r hl hr hlt htr.le prev bs hb
  refine stripGains_le t τ prev bs h.1 (collisionTwice_nonneg _ _ (by exact_mod_cast hM)) ?_
  intro b hmem hbot htop
  exact certified_gain s l r b hs hrows hM hl hr hlt htr hbot htop (h.2 b hmem).1

end PiPolynomialValues.PrimeWindow
