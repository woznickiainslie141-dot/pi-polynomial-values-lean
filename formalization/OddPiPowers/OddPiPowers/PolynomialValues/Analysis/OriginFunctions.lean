module

public import OddPiPowers.PolynomialValues.Analysis.DividedTaylor

/-! Pointwise functions analytic at zero form a ring in which divisibility
by the coordinate records an actual analytic factor. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

noncomputable def originRing : Subring (ℂ → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  zero_mem' := analyticAt_const
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  neg_mem' := fun hf => hf.neg
  mul_mem' := fun hf hg => hf.mul hg

abbrev OriginFunction := ↥originRing

noncomputable def originCoordinate : OriginFunction := ⟨id,analyticAt_id⟩

noncomputable def originConst (c : ℂ) : OriginFunction := ⟨fun _ => c,analyticAt_const⟩

noncomputable def originEval (z : ℂ) : OriginFunction →+* ℂ :=
  (Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp originRing.subtype

theorem originCoordinate_dvd (p : OriginFunction) (hp : p.val 0=0) : originCoordinate ∣ p := by
  obtain ⟨g,hg,h⟩ := (show AnalyticAt ℂ p.val 0 from p.property).exists_eq_sum_add_pow_mul 1
  refine ⟨⟨g,hg⟩,Subtype.ext (funext fun z => ?_)⟩
  change p.val z = z*g z
  simpa [hp,smul_eq_mul] using h z

noncomputable def pathTaylorRow (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (p : OriginFunction) (hp : p.val 0=0) (s : ℕ) : OriginFunction :=
  ⟨fun z => dividedRow s f (p.val z),by
    have h : AnalyticAt ℂ (dividedRow s f) 0 := analyticAt_const.mul (analytic_iterated_at_zero hf s)
    have h' : AnalyticAt ℂ (dividedRow s f) (p.val 0) := hp.symm ▸ h
    exact h'.comp (show AnalyticAt ℂ p.val 0 from p.property)⟩

theorem pathTaylorRow_truncation (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (p : OriginFunction) (hp : p.val 0=0) (s H K : ℕ) (hs : s+H ≤ K) :
    originCoordinate^H ∣ pathTaylorRow f hf p hp s -
      ∑ k : Fin K, originConst (iteratedDeriv k.val f 0)*
        (originConst (jetCoefficient s k.val)*p^(k.val-s)) := by
  obtain ⟨g,hg,he⟩ := dividedTaylor hf s K (by omega)
  let G : OriginFunction := ⟨fun z => g (p.val z),
    (show AnalyticAt ℂ g (p.val 0) from hp.symm ▸ hg).comp (show AnalyticAt ℂ p.val 0 from p.property)⟩
  apply (pow_dvd_pow originCoordinate (show H ≤ K-s by omega)).trans
  apply (pow_dvd_pow_of_dvd (originCoordinate_dvd p hp) (K-s)).trans
  refine ⟨G,Subtype.ext (funext fun z => ?_)⟩
  change originEval z (pathTaylorRow f hf p hp s-
      ∑ k : Fin K, originConst (iteratedDeriv k.val f 0)*
        (originConst (jetCoefficient s k.val)*p^(k.val-s))) = originEval z (p^(K-s)*G)
  simp only [map_sub,map_sum,map_mul,map_pow]
  change dividedRow s f (p.val z)-(∑ k : Fin K, iteratedDeriv k.val f 0*(jetCoefficient s k.val*p.val z^(k.val-s))) =
    p.val z^(K-s)*g (p.val z)
  rw [Fin.sum_univ_eq_sum_range (fun k => iteratedDeriv k f 0*(jetCoefficient s k*p.val z^(k-s))) K]
  simp only [← mul_assoc]
  exact sub_eq_iff_eq_add'.mpr (he _)

end PiPolynomialValues.FourPeriod
