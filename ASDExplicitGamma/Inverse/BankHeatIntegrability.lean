module

public import ASDExplicitGamma.Gaussian.LawTransfer
public import ASDExplicitGamma.Gaussian.ModelHeat

/-! Integrability of signed polynomial observables on the actual insertion law. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian

/-- Polynomial growth and the physical q3 law give actual-model integrability,
including signed covariance traces; no one-sided generator bound is used. -/
theorem bank_model_heat_integrable (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell)) (Φ : C(K,ℝ) → ℝ)
    (hΦ : Measurable Φ) (hg : HasPolynomialGrowth Φ) (t : ℝ) :
    Integrable (fun ω => Φ (modelInsertedScalar K m t ω)) (Cutoff.cutoffSampleLaw M).toMeasure := by
  obtain ⟨T,v,hA,hlaw⟩ := freshShell_map_scalarRestriction_eq_gaussianSeries M h hM m (K:=K)
  have hY : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction K (ω.1 (m+1))) :=
    (measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (m+1)).comp measurable_subtype_coe)
  exact (integral_independent_insertion (Cutoff.cutoffSampleLaw M).toMeasure
    (olderField K m) _ (measurable_olderField K ell m hK) hY
    (indepFun_olderField_freshShell K M ell m hK) hA T hlaw
    (integrable_polynomial_olderFieldLaw K M ell m hK) Φ hΦ hg t).1

end ASDExplicitGamma.Inverse
