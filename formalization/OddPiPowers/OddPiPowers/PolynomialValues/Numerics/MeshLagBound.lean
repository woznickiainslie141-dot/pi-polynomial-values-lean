module

public import OddPiPowers.PolynomialValues.Numerics.EnergyBasis
public import OddPiPowers.PolynomialValues.Numerics.SignedMeshSamples
public import OddPiPowers.PolynomialValues.Analysis.EdgeCharge

/-! A certified word bounds the true second-primitive interaction of all
pairs of jumps, for either orientation of the energy inequality. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Certificates

theorem meshJ_word_range (k : ℕ) (hk : k≤80000) : |primitiveMesh.lookupJ k|≤10^17 := by
  let x := (k : ℝ)/40000
  have hx : 0≤x := by dsimp [x]; positivity
  have ht : (k : ℝ)≤80000 := by exact_mod_cast hk
  have hx2 : x≤2 := by dsimp [x]; linarith only [ht]
  obtain ⟨hl,hu,hj,hj'⟩ := primitiveMesh_enclosed k hk
  change (primitiveMesh.lookupF k : ℝ)≤10^9*logPrimitive x at hl
  change 10^9*logPrimitive x≤(primitiveMesh.lookupF k : ℝ)+2 at hu
  change (primitiveMesh.lookupJ k : ℝ)≤10^12*energyPrimitive x at hj
  change 10^12*energyPrimitive x≤(primitiveMesh.lookupJ k : ℝ)+2 at hj'
  have hF : |(primitiveMesh.lookupF k : ℝ)|≤(2:ℝ)^31 := by exact_mod_cast meshF_word_range k hk
  have hf := abs_le.mp hF
  have habs : |logPrimitive x|≤3 := by rw [abs_le]; constructor <;> linarith only [hf.1,hf.2,hl,hu]
  have hp := mul_le_mul (by simpa only [abs_of_nonneg hx] using hx2 : |x|≤2) habs (abs_nonneg _) (by norm_num)
  rw [← abs_mul] at hp
  have hp' := abs_le.mp hp
  have hsq : x^2≤4 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hx2) (show 0≤2+x by linarith)]
  have he : energyPrimitive x=x*logPrimitive x/2-x^2/4 := by unfold energyPrimitive logPrimitive; ring
  rw [he] at hj hj'
  have h : |(primitiveMesh.lookupJ k : ℝ)|≤(10:ℝ)^17 := by
    rw [abs_le]
    constructor <;> linarith only [hj,hj',hp'.1,hp'.2,hsq,sq_nonneg x]
  exact_mod_cast h

theorem positiveLag_last {n k : ℕ} (h : n≤k+1) (a : ℕ → ℤ) : positiveLag n a k=0 := by
  unfold positiveLag
  exact sum_eq_zero (fun i _ => if_neg (by omega))

theorem energyPrimitive_grid (step i j : ℕ) :
    energyPrimitive (((i : ℝ)-j)*step/40000) =
      energyPrimitive ((((i : ℤ)-j).natAbs : ℝ)*step/40000) := by
  have h : ((((i : ℤ)-j).natAbs : ℕ) : ℝ)=|(i : ℝ)-j| := by
    rw [← Int.cast_natCast (R := ℝ),Int.natCast_natAbs,Int.cast_abs,Int.cast_sub,Int.cast_natCast,Int.cast_natCast]
  rw [h]
  by_cases hh : 0≤(i : ℝ)-j
  · rw [abs_of_nonneg hh]
  · rw [abs_of_nonpos (le_of_not_ge hh),neg_mul,neg_div,energyPrimitive_neg]

noncomputable def meshPairEnergy (n step : ℕ) (d : ℕ → ℤ) : ℝ :=
  ∑ i ∈ range n, ∑ j ∈ range n, (d i : ℝ)*d j*energyPrimitive (((i : ℝ)-j)*step/40000)

theorem signed_mesh_energy_upper {n step : ℕ} (hn : 0<n) (hN : n≤80001) (hgrid : (n-1)*step≤80000)
    (a : ℕ → ℤ) (sign : ℤ) (hs : |sign|≤1) (h₁ : ∀ i<n, |a i|≤10^13)
    (h₂ : ∑ j ∈ range n, |a (n-1-j)|≤10^13) {x rev wj : ℤ}
    (hx : x=packEval energyBase n a) (hr : rev=packEval energyBase n (fun j => a (n-1-j)))
    (hj : wj=packEval energyBase n (fun j => lagPrimitive n step (n-1-j))) :
    (sign : ℝ)*10^12*meshPairEnergy n step a≤(lagEnergyWord n x rev wj sign : ℝ) := by
  have hkgrid (k : ℕ) (h : k+1<n) : (k+1)*step≤80000 :=
    (Nat.mul_le_mul_right step (show k+1≤n-1 by omega)).trans hgrid
  have hJ (k : ℕ) (_ : k<n) : |lagPrimitive n step k|≤10^17 := by
    by_cases h : k+1<n
    · simpa [lagPrimitive,h] using meshJ_word_range ((k+1)*step) (hkgrid k h)
    · simp [lagPrimitive,h]
  have h0 : energyPrimitive ((0:ℕ)*((step:ℝ))/40000)=0 := by simp [energyPrimitive]
  have he := mesh_energy_lags n a (fun t => energyPrimitive ((t : ℝ)*step/40000)) h0
  unfold meshPairEnergy
  simp_rw [energyPrimitive_grid]
  rw [he,mul_sum,lagEnergyWord_sound hn hN a _ sign hs h₁ h₂ hJ hx hr hj,Int.cast_sum]
  apply sum_le_sum
  intro k _
  by_cases h : k+1<n
  · obtain ⟨_,_,hl,hu⟩ := primitiveMesh_enclosed ((k+1)*step) (hkgrid k h)
    have H := signed_primitive_allowance ((2*sign)*positiveLag n a k) _ _ hl hu
    simp only [lagPrimitive,if_pos h]
    convert H using 1
    push_cast
    ring
  · simp [positiveLag_last (by omega : n≤k+1) a]

end PiPolynomialValues
