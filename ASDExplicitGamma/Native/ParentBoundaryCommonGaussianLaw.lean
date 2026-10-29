module

public import ASDExplicitGamma.Native.ParentBoundaryCommonGaussianMap
public import ASDExplicitGamma.Inverse.SourceQ3CovarianceLaw
public import ASDExplicitGamma.Gaussian.FiniteFactorLaw

/-! The actual common-center observed shell law has the complete physical covariance. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

local instance parentCommonGaussianLawCompact (P : TriadicCube 2) : CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure
local instance parentCommonGaussianLawMeasurable (Q : TriadicCube 2) :
    MeasurableSpace (ResponseCoefficient (openCubeSet Q)) := borel _
local instance parentCommonGaussianLawBorel (Q : TriadicCube 2) :
    BorelSpace (ResponseCoefficient (openCubeSet Q)) := ⟨rfl⟩

/-- Any genuine actual-shell realization gives the exact physical common-center
covariance contraction on the observed descendant. The same original source
center and whole cutoff sample law are used on both sides. -/
theorem parent_boundary_common_observed_shell_covariance
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d) (J : ℤ)
    (T : GaussianFactorL2 ℕ →L[ℝ] C(closure (cubeSet P),ℝ))
    (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖^2))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction (closure (cubeSet P)) (ω.1 J)) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (Φ : ResponseCoefficient (openCubeSet Q) → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (x : ResponseCoefficient (openCubeSet Q)) :
    modelCovarianceTrace Φ (fun j => parentBoundaryCommonObservedMap hQ (T (v j))) x =
      modelCovarianceTrace Φ (parentBoundaryCommonResponseDirections P Q
        (q3ModelAmplitude M h J) (q3ModelLength J)) x := by
  let K := closure (cubeSet P)
  obtain ⟨ell,hP⟩ := exists_originCube_containing_compact K (isBounded_cubeSet P).isCompact_closure
  let K' := closure (cubeSet (originCube 2 ell))
  let b := q3ModelAmplitude M h J
  let L := q3ModelLength J
  let R := parentBoundaryCommonEnclosingRestriction P ell hP
  let B := parentBoundaryCommonObservedMap hQ
  have hactual : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K' (ω.1 J)) =
      standardGaussianInfinitePi.map (mainCubeQ3Series ell b L) := by
    simpa only [sub_add_cancel] using main_actual_fresh_cube_factor_law ell M h hM (J-1)
  have hmeas := @stronglyMeasurable_gaussianSeriesLimitE
    (MainCubeH3 ell b L) C(K',ℝ)
    inferInstance (mainCubeH3InnerProductSpace ell b L) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (mainCubeQ3Directions ell b L) (mainCubeQ3Directions_summable ell b L) (mainCubeH3Value ell b L)
  change StronglyMeasurable (mainCubeQ3Series ell b L) at hmeas
  have hXmeas : Measurable (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K' (ω.1 J)) :=
    (measurable_shellFieldScalarRestriction _).comp ((measurable_pi_apply J).comp measurable_subtype_coe)
  have hmapR := congrArg (fun μ : Measure C(K',ℝ) => μ.map R) hactual
  rw [Measure.map_map R.continuous.measurable hXmeas,
    Measure.map_map R.continuous.measurable hmeas.measurable] at hmapR
  have hrestrict : (fun ω : Cutoff.CutoffSample 2 => R (shellFieldScalarRestriction K' (ω.1 J))) =
      fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 J) := by
    funext ω
    ext y
    rfl
  simp only [Function.comp_def] at hmapR
  rw [hrestrict] at hmapR
  have hcanonical : standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) =
      standardGaussianInfinitePi.map (fun ω => R (mainCubeQ3Series ell b L ω)) := hlaw.symm.trans hmapR
  have hRmeas : Measurable (fun ω => R (mainCubeQ3Series ell b L ω)) :=
    R.continuous.measurable.comp hmeas.measurable
  have hmap := congrArg (fun μ : Measure C(K,ℝ) => μ.map B) hcanonical
  rw [Measure.map_map B.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable,
    Measure.map_map B.continuous.measurable hRmeas] at hmap
  have htrace := @modelCovarianceTrace_eq_of_law
    (GaussianFactorL2 ℕ) (MainCubeH3 ell b L) (ResponseCoefficient (openCubeSet Q))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance (mainCubeH3InnerProductSpace ell b L) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    v hA (B.comp T) (mainCubeQ3Directions ell b L) (mainCubeQ3Directions_summable ell b L)
    (B.comp (R.comp (mainCubeH3Value ell b L))) hmap Φ hΦ x
  calc
    _ = modelCovarianceTrace Φ (fun j => B (R (pureFluxMainCubeQ3Directions ell b L j))) x := htrace
    _ = _ := by
      congr 1
      funext j
      exact parent_boundary_common_gaussian_directions_eq hQ ell hP b L j

end
end ASDExplicitGamma.Native
