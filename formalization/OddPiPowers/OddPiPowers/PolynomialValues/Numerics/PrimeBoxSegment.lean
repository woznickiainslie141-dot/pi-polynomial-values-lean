module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBox

/-! Join adjacent batches of checked trapezoids while retaining the previous
right endpoint and the exact credit and count of all their boxes. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

def slabEnd (prev : Abscissa) : List Slab → Abscissa
  | [] => prev
  | s :: ss => slabEnd s.right ss

structure CheckedSlabs (s : Shape) (left right : Abscissa) (xs : List Slab)
    (boxes credit : ℕ) : Prop where
  valid : slabsPass s left xs = true
  last : slabEnd left xs = right
  count_eq : (xs.map (fun sl => sl.boxes.length)).sum = boxes
  credit_eq : (xs.map Slab.credit).sum = credit

private theorem slabsPass_append (s : Shape) (l : Abscissa) (xs ys : List Slab) :
    slabsPass s l (xs ++ ys) = (slabsPass s l xs && slabsPass s (slabEnd l xs) ys) := by
  induction xs generalizing l with
  | nil => simp [slabsPass, slabEnd]
  | cons x xs ih => simp only [List.cons_append, slabsPass, slabEnd, ih, Bool.and_assoc]

private theorem slabEnd_append (l : Abscissa) (xs ys : List Slab) :
    slabEnd l (xs ++ ys) = slabEnd (slabEnd l xs) ys := by
  induction xs generalizing l with
  | nil => rfl
  | cons x xs ih => exact ih x.right

theorem CheckedSlabs.append {s : Shape} {l m r : Abscissa} {xs ys : List Slab}
    {a b u v : ℕ} (hx : CheckedSlabs s l m xs a u) (hy : CheckedSlabs s m r ys b v) :
    CheckedSlabs s l r (xs ++ ys) (a+b) (u+v) := by
  exact ⟨by rw [slabsPass_append, hx.valid, hx.last, hy.valid]; rfl,
    by rw [slabEnd_append, hx.last, hy.last],
    by rw [List.map_append, List.sum_append, hx.count_eq, hy.count_eq],
    by rw [List.map_append, List.sum_append, hx.credit_eq, hy.credit_eq]⟩

end PiPolynomialValues.PrimeWindow
