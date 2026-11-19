module

public import OddPiPowers.PolynomialValues.Numerics.PrimeTailRate
public import OddPiPowers.PolynomialValues.Numerics.PrimeSupport

/-! Use exactly the listed interval at each labeled level and commute
the finite prime and level sums before applying the prime number theorem. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter
open scoped Topology

def cutAt (ls : List ℚ) (u : ℕ) : ℚ := ls[u]?.getD 0

theorem cutAt_mem {ls : List ℚ} {u : ℕ} (hu : u < ls.length) : cutAt ls u ∈ ls := by
  simp [cutAt,List.getElem?_eq_getElem hu,List.getElem_mem]

noncomputable def activeLevels (ls : List ℚ) (r : ℚ) (N p : ℕ) : Finset ℕ :=
  (range ls.length).filter fun u => p ∈ primeSlice (cutAt ls u) r N

theorem activeLevels_card (ls : List ℚ) (r : ℚ) (N p : ℕ) : (activeLevels ls r N p).card ≤ ls.length := by
  simpa only [activeLevels,card_range] using card_le_card (filter_subset (fun u => p ∈ primeSlice (cutAt ls u) r N) (range ls.length))

theorem sum_activeLevels {M : Type*} [AddCommMonoid M] (ls : List ℚ) (r : ℚ) (N : ℕ)
    (P : Finset ℕ) (f : ℕ → ℕ → M)
    (hs : ∀ u < ls.length, primeSlice (cutAt ls u) r N ⊆ P) :
    (∑ p ∈ P, ∑ u ∈ activeLevels ls r N p, f p u) =
      ∑ u ∈ range ls.length, ∑ p ∈ primeSlice (cutAt ls u) r N, f p u := by
  classical
  simp only [activeLevels,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [← sum_filter]
  have he : P.filter (fun p => p ∈ primeSlice (cutAt ls u) r N) = primeSlice (cutAt ls u) r N := by
    ext p
    exact mem_filter.trans ⟨And.right,fun hp => ⟨hs u (mem_range.mp hu) hp,hp⟩⟩
  rw [he]

theorem sum_cutAt {M : Type*} [AddCommMonoid M] (ls : List ℚ) (f : ℚ → ℕ → M) :
    (∑ u ∈ range ls.length, f (cutAt ls u) u) = (ls.zipIdx.map (fun e => f e.1 e.2)).sum := by
  rw [← Fin.sum_univ_eq_sum_range (fun u => f (cutAt ls u) u) ls.length,← Fin.sum_ofFn]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hx : i < ls.length := by simpa using hi
    simp [cutAt,List.getElem?_eq_getElem hx]

theorem massScale_tendsto (s : Shape) (hm : 0 < s.massUnit) :
    Tendsto (fun t : ℕ => s.massUnit*t) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with t ht
  exact ht.trans (by simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ s.massUnit from hm))

noncomputable def aggregateTail (s : Shape) (ls : List ℚ) (N : ℕ) : ℝ :=
  ∑ u ∈ range ls.length, primeAverage (cutAt ls u) s.largestRowQ (s.netTailValue (u+1)) N

theorem aggregateTail_tendsto (s : Shape) (ls : List ℚ)
    (hls : ∀ q ∈ ls, 0 < q ∧ q ≤ s.largestRowQ) :
    Tendsto (aggregateTail s ls) atTop (𝓝 (s.selectedTailIntegral ls : ℝ)) := by
  have h (u : ℕ) (hu : u ∈ range ls.length) :=
    s.netTail_prime_rate (u+1) (hls _ (cutAt_mem (mem_range.mp hu))).1 (hls _ (cutAt_mem (mem_range.mp hu))).2
  have he : (s.selectedTailIntegral ls : ℝ) =
      ∑ u ∈ range ls.length, (s.netTailIntegral (u+1) (cutAt ls u) s.largestRowQ : ℝ) := by
    unfold Shape.selectedTailIntegral
    rw [← sum_cutAt ls (fun q u => s.netTailIntegral (u+1) q s.largestRowQ),Rat.cast_sum]
  rw [he]
  exact tendsto_finsetSum _ h

end PiPolynomialValues.FourPeriod
