module

public import ASDExplicitGamma.Native.HeatIndividualRareRounding
public import ASDExplicitGamma.Native.HeatIndividualOldCertificates

/-! Actual correlated rare moments consumed by all153 individual source rows. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native MeasureTheory
open scoped ENNReal
noncomputable section

/-- The selected configured OLD row pays each actual rare monomial. No
independence is assumed between the reserve and the evolved trace; all306
top-degree root certificates are supplied internally. -/
theorem heat_configured_individual_rare_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (index : Fin 153) (R T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ z,0 ≤ R z) (hT0 : ∀ z,0 ≤ T z)
    (j : Fin 2) (l : ℕ) (hl : l ≤ 20)
    (hRc : eLpNorm' R 128 μ ≤ ENNReal.ofReal (nativeEps:ℝ))
    (h20 : eLpNorm' T 20 μ ≤ ENNReal.ofReal ((nativeOld (nativeConfiguredSystem index).gap).x:ℝ))
    (h128 : eLpNorm' T 128 μ ≤ ENNReal.ofReal ((nativeOld (nativeConfiguredSystem index).gap).f:ℝ)) :
    Integrable (fun z => R z^(j.val+1)*T z^l) μ ∧
      (∫ z,R z^(j.val+1)*T z^l ∂μ) ≤
        (nativeRareJ (nativeOld (nativeConfiguredSystem index).gap).x
          (nativeOld (nativeConfiguredSystem index).gap).f (j.val+1) l:ℝ) := by
  obtain ⟨he,hx,hf,hroot1,hroot2⟩ := heat_configured_individual_old_valid index
  have hroot : nativeRootValid
      (((nativeOld (nativeConfiguredSystem index).gap).f /
        (nativeOld (nativeConfiguredSystem index).gap).x)^(5*(j.val+1))) 27 = true := by
    fin_cases j
    · exact hroot1
    · exact hroot2
  have hmoment := heat_remainder_rare_moment_le_J μ R T hR hT hR0 hT0 j l hl
    nativeEps (nativeOld (nativeConfiguredSystem index).gap).x
    (nativeOld (nativeConfiguredSystem index).gap).f
    (by norm_num [nativeEps]) (by exact_mod_cast hx) (by exact_mod_cast hf) hRc h20 h128
  exact ⟨hmoment.1,hmoment.2.trans (heat_individual_rareJ_le _ _ hx hf (j.val+1) l hl hroot)⟩

end
end ASDExplicitGamma.Native
