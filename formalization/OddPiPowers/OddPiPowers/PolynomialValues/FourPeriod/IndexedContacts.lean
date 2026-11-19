module

public import OddPiPowers.PolynomialValues.FourPeriod.ContactBudget

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

/-- The local degree budget with the actual centres and rows indexed by the
same finite type. Distinct centres ensure that no root is counted twice. -/
theorem indexed_contact_sum_le_band {ι : Type*} [Fintype ι] [Nonempty ι] {J : ℕ}
    (S : Finset ℤ) (p : ℤ → ℂ[X]) (U : ℕ) (B : Fin (J+1) → ℕ)
    (hB : ∀ k, B k ≤ U) (hb : ∀ k, InBand S p k.val (B k))
    (hl : ∀ t ∈ S, 0 ≤ t+(U : ℤ)) (hd : ∀ t ∈ S, (p t).natDegree ≤ J)
    {t₀ : ℤ} (ht : t₀ ∈ S) (hp : p t₀ ≠ 0) (hdeg : (p t₀).natDegree = J)
    (centre : ι → ℂ) (hc : Function.Injective centre) (hn : ∀ i, centre i ≠ 0)
    (shift : ι → Fin (J+1) → ℂ) (hs : ∀ i, Function.Injective (shift i))
    (ord : ι → Fin (J+1) → ℕ) (hv : ∀ r i, (PowerSeries.X : PowerSeries ℂ)^(ord r i) ∣
      translatedTrajectory (centre r) (shift r i) S p) :
    ∑ r, ∑ i, (ord r i-J) ≤ ∑ k, 2*B k := by
  classical
  let points := Finset.univ.image centre
  let idx := Function.invFun centre
  have hbck (r : ι) : idx (centre r) = r := Function.leftInverse_invFun hc r
  have hpoints {ρ : ℂ} (h : ρ ∈ points) : ∃ i, centre i = ρ := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    exact ⟨i,hi⟩
  have h := selected_contact_sum_le_band S p U B hB hb hl hd ht hp hdeg points
    (fun ρ hρ => by obtain ⟨i,rfl⟩ := hpoints hρ; exact hn i)
    (fun ρ => shift (idx ρ))
    (fun ρ hρ => by obtain ⟨i,rfl⟩ := hpoints hρ; simpa only [hbck] using hs i)
    (fun ρ => ord (idx ρ))
    (fun ρ hρ j => by obtain ⟨i,rfl⟩ := hpoints hρ; simpa only [hbck] using hv i j)
  dsimp only [points] at h
  rw [Finset.sum_image (fun _ _ _ _ he => hc he)] at h
  simpa only [hbck] using h

end PiPolynomialValues.FourPeriod
