module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence

/-! Pair the ordinary and priced spatial certificates belonging to each
individual angular label, including the unpriced labels on the lower face. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod

def LabelReferencePair (s : Shape) (a : AnchorPlan) (t : AngleLabel) : Prop :=
  Nonempty (ReferenceEvidence s a t.slopes 0 t.ordinary) ∧ Nonempty (ReferenceEvidence s a t.slopes t.price t.tilted)

theorem labelPairs_cons {s : Shape} {a : AnchorPlan} {t : AngleLabel} {ts : List AngleLabel}
    (ht : LabelReferencePair s a t) (hs : ∀ u∈ts, LabelReferencePair s a u) :
    ∀ u∈t::ts, LabelReferencePair s a u := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl|hm
  · exact ht
  · exact hs u hm

end PiPolynomialValues
