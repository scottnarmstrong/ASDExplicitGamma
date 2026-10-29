module

public import ASDExplicitGamma.Inverse.StoppedLocalizedLocality
public import ASDExplicitGamma.Inverse.StoppedLocalizationColors

/-! Joint independence of the actual localized diameter powers within each source color. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model
noncomputable section

/-- Every finite same-color family of actual localized diameter powers is
jointly independent, by the full completed cutoff restriction theorem. -/
theorem q3_localized_powers_independent {I : Type} [Fintype I]
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (j : ℤ) (τ η : ℝ)
    (M m : ℕ) (x : I → BlockSite) (hx : Function.Injective x)
    (c : LocalizationColor M) (hc : ∀ i, localizationColor M (x i) = c) :
    iIndepFun (fun i ω => (realLocalizedDiameterField (q3PlanarMarks A j τ η) M (3^M) (x i) ω)^m)
      (Cutoff.cutoffSampleLaw A).toMeasure := by
  apply restriction_local_observables_independent A h hA (j+40+M)
    (fun i => localizedPhysicalRegion j M (x i))
    (fun i => localized_physical_region_measurable j M (x i))
  · intro i k hik p hp r hr
    have hgap := localization_color_separation M (x i) (x k) (fun he => hik (hx he))
      ((hc i).trans (hc k).symm)
    exact localized_physical_regions_separated j M (x i) (x k) hgap hp hr
  · intro i
    let localizedInfo : MeasurableSpace (Cutoff.CutoffSample 2) :=
      Cutoff.cutoffSampleLocalSigma A (j+40+M) (localizedPhysicalRegion j M (x i))
    exact (q3_real_localized_diameter_local A j τ η M (x i)).pow_const m

/-- The literal (7N)^2 source color partition, for any finite injectively
indexed physical block population. No cross-color independence is asserted. -/
theorem q3_localized_powers_colored_independent {I : Type} [Fintype I]
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (j : ℤ) (τ η : ℝ)
    (M m : ℕ) (x : I → BlockSite) (hx : Function.Injective x) (c : LocalizationColor M) :
    iIndepFun (fun i : {i // localizationColor M (x i) = c} =>
      fun ω => (realLocalizedDiameterField (q3PlanarMarks A j τ η) M (3^M) (x i.val) ω)^m)
        (Cutoff.cutoffSampleLaw A).toMeasure :=
  q3_localized_powers_independent (I := {i : I // localizationColor M (x i) = c})
    A h hA j τ η M m (fun i : {i : I // localizationColor M (x i) = c} => x i.val)
    (hx.comp Subtype.val_injective) c (fun i => i.property)

end
end ASDExplicitGamma.Inverse
