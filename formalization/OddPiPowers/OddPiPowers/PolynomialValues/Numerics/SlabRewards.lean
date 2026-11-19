module

public import OddPiPowers.PolynomialValues.Numerics.FinitePrimeBudget
public import OddPiPowers.PolynomialValues.Numerics.PrimeSupport

/-! Count the usable residue saving without double counting among prime
windows. The finite definition works at every scale, including zero. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod Finset

def Slab.Eligible (z : Slab) (s : Shape) (K t p : ℕ) : Prop :=
  2 < p ∧ primeCeiling s t < p^2 ∧ ∃ δ : ℝ, 0 < δ ∧
    z.left.value+δ ≤ ((s.massUnit*t : ℕ) : ℝ)/p ∧
    ((s.massUnit*t : ℕ) : ℝ)/p ≤ z.right.value-δ ∧
    ∀ i ∈ s.rows, (K : ℝ) < rowRate s i*δ*p

noncomputable def Slab.reward (z : Slab) (s : Shape) (K t p : ℕ) : ℕ := by
  classical
  exact if z.Eligible s K t p then latticeSaving z.boxes (s.massUnit*t) p else 0

noncomputable def residueReward (xs : List Slab) (s : Shape) (K t p : ℕ) :=
  (xs.map (fun z => z.reward s K t p)).sum

structure Slab.Checked (z : Slab) (s : Shape) (floor : ℝ) : Prop where
  left_num : 0 < z.left.num
  right_num : 0 < z.right.num
  left_den : 0 < z.left.den
  right_den : 0 < z.right.den
  starts : floor ≤ z.left.value
  interior : z.left.value < z.right.value
  ends : z.right.value ≤ 100
  boxes_ok : boxesPass s z.left z.right ⟨0,0⟩ z.boxes = true

theorem Slab.checked_of_valid {z : Slab} {s : Shape} {prev : Abscissa} (hp : 0 < prev.den)
    (h : z.validAfter s prev = true) : z.Checked s prev.value := by
  simp only [Slab.validAfter,Bool.and_eq_true] at h
  have h' := h
  obtain ⟨ha,hb,hc,hd,he,hf,hg⟩ := of_decide_eq_true h'.1
  have h₁ : (0 : ℝ) < prev.den := by exact_mod_cast hp
  have h₂ : (0 : ℝ) < z.left.den := by exact_mod_cast hc
  have h₃ : (0 : ℝ) < z.right.den := by exact_mod_cast hd
  refine ⟨ha,hb,hc,hd,?_,?_,?_,h'.2⟩
  · exact (div_le_div_iff₀ h₁ h₂).mpr (by exact_mod_cast he)
  · exact (div_lt_div_iff₀ h₂ h₃).mpr (by exact_mod_cast hf)
  · exact (div_le_iff₀ h₃).mpr (by exact_mod_cast hg)

theorem Slab.Checked.lower {z : Slab} {s : Shape} {x y : ℝ} (h : z.Checked s y) (hxy : x ≤ y) :
    z.Checked s x := {h with starts := hxy.trans h.starts}

theorem checked_in_slabs (xs : List Slab) (s : Shape) (prev : Abscissa) (hp : 0 < prev.den)
    (h : slabsPass s prev xs = true) : ∀ z ∈ xs, z.Checked s prev.value := by
  induction xs generalizing prev with
  | nil => simp
  | cons z zs ih =>
    simp only [slabsPass,Bool.and_eq_true] at h
    obtain ⟨hc,ht⟩ := h
    have he := Slab.checked_of_valid hp hc
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hm
    · exact he
    · exact (ih z.right he.right_den ht u hm).lower (he.starts.trans he.interior.le)

theorem residueReward_below (xs : List Slab) (s : Shape) (K t p : ℕ) (prev : Abscissa)
    (hp : 0 < prev.den) (h : slabsPass s prev xs = true)
    (hr : ((s.massUnit*t : ℕ) : ℝ)/p ≤ prev.value) : residueReward xs s K t p = 0 := by
  have hz (z : Slab) (hm : z ∈ xs) : z.reward s K t p = 0 := by
    have hleft := (checked_in_slabs xs s prev hp h z hm).starts
    have hn : ¬ z.Eligible s K t p := by
      rintro ⟨_,_,δ,hd,hl,_⟩
      linarith
    simp [Slab.reward,hn]
  unfold residueReward
  exact List.sum_eq_zero (fun x hx => by obtain ⟨z,hm,rfl⟩ := List.mem_map.mp hx; exact hz z hm)

theorem residueReward_single (xs : List Slab) (s : Shape) (K t p : ℕ) (prev : Abscissa)
    (hp : 0 < prev.den) (h : slabsPass s prev xs = true) :
    residueReward xs s K t p = 0 ∨ ∃ z ∈ xs, z.Eligible s K t p ∧
      residueReward xs s K t p = latticeSaving z.boxes (s.massUnit*t) p := by
  classical
  induction xs generalizing prev with
  | nil => exact Or.inl rfl
  | cons z zs ih =>
    simp only [slabsPass,Bool.and_eq_true] at h
    obtain ⟨hc,ht⟩ := h
    have he := Slab.checked_of_valid hp hc
    change z.reward s K t p + residueReward zs s K t p = 0 ∨ _
    by_cases hz : z.Eligible s K t p
    · obtain ⟨δ,hd,_,hr,_⟩ := hz.2.2
      have hzero := residueReward_below zs s K t p z.right he.right_den ht (by linarith)
      refine Or.inr ⟨z,by simp,hz,?_⟩
      change z.reward s K t p + residueReward zs s K t p = _
      rw [hzero,add_zero,Slab.reward,if_pos hz]
    · have hzero : z.reward s K t p = 0 := by simp [Slab.reward,hz]
      rcases ih z.right he.right_den ht with hnil|⟨u,hu,he',hs⟩
      · exact Or.inl (by rw [hzero,hnil,zero_add])
      · refine Or.inr ⟨u,List.mem_cons_of_mem _ hu,he',?_⟩
        change z.reward s K t p + residueReward zs s K t p = _
        rw [hzero,zero_add,hs]

end PiPolynomialValues.PrimeWindow
