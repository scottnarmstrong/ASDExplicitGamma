module

public import ASDExplicitGamma.Native.HeatVHEATSourceRow
public import ASDExplicitGamma.Inverse.SourceQ3CovarianceLaw
public import ASDExplicitGamma.Gaussian.BilinearCovariance
public import ASDExplicitGamma.Main.CubeFactor

/-! Transport the full real-power source generator row through the actual
fresh-shell Gaussian law. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Main
open ASDExplicitGamma.Model
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped ENNReal

/-- The actual fresh-shell law transports the source covariance drift and
the full gradient bracket as separate rows. The covariance row retains the
signed center/mixed/remainder estimate; consumers can assemble the bracket
with their own actual carrier decomposition. -/
def nativeHeatSourceDriftAndBracketConclusion
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (s : ℕ) (σ : ℝ)
    (T : GaussianFactorL2 ℕ →L[ℝ]
      C(closure (cubeSet (originCube 2 n)), ℝ))
    (v : ℕ → GaussianFactorL2 ℕ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) : Prop :=
  let Q := originCube 2 n
  let Φ := modelTraceObservable n M.nu σ
  let k := pureFluxOpenResponseRestriction n x
  let Bmix := lemmaVTileHistory Q (pureFluxBankSourceDepth s)
    (responseFramePlanarCoefficientField M.nu σ k)
  let Brem := pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
    (responseFramePlanarCoefficientField M.nu σ k)
  let B := max Bmix Brem
  let ρ := cubeScaleFactor Q /
    (q3ModelLength (n + (s : ℤ))).1
  let δ := diagMeshRadius Q (pureFluxBankSourceDepth s) /
    (q3ModelLength (n + (s : ℤ))).1
  let κ := lemmaVH2kn ρ δ
  let κB := lemmaVH2Bn ρ δ
  let μ := pureFluxCovarianceMu (pureFluxCovarianceA 0 (s - 1))
    (pureFluxCovarianceB 0 (s - 1))
  let v₀ := (q3ModelAmplitude M h (n + (s : ℤ))) ^ 2 / σ ^ 2
  let Acoef := coarseBlockMatrix (cubeSet Q)
    (responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet Q)) ℝ ℝ x))
  let D := Matrix.trace (frameMatrix σ Acoef).lowerRight
  ((1 / 2 : ℝ) * modelCovarianceTrace Φ (fun j => T (v j)) x ≤
      v₀ * D + (2 * v₀ * κ * B + v₀ * μ * B ^ 2) * (Φ x + 4)) ∧
    (modelGradientSquareTrace Φ (fun j => T (v j)) x ≤
      4 * v₀ * Φ x * ((1 + κ) * D +
        (κB ^ 2 + κ) * B ^ 2 * (Φ x + 4)))

/-- Separate signed drift and bracket bounds for any Gaussian-series
realization of the actual fresh-shell law. -/
theorem nativeHeat_sourceFreshShellDriftAndBracket_le_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (σ : ℝ) (hσ : 0 < σ)
    (T : GaussianFactorL2 ℕ →L[ℝ]
      C(closure (cubeSet (originCube 2 n)), ℝ))
    (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖ ^ 2))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 n))) (ω.1 (n + (s : ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    nativeHeatSourceDriftAndBracketConclusion M h n s σ T v x := by
  classical
  unfold nativeHeatSourceDriftAndBracketConclusion
  intro Q Φ k Bmix Brem B ρ δ κ κB μ v₀ Acoef D
  let b := q3ModelAmplitude M h (n + (s : ℤ))
  let L := q3ModelLength (n + (s : ℤ))
  let K := closure (cubeSet (originCube 2 n))
  let H := pureFluxMainCubeQ3Directions n b L
  have hactual : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K
        (ω.1 (n + (s : ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := hlaw
  have htime : n + (s : ℤ) - 1 + 1 = n + (s : ℤ) := by omega
  have hsource : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K
        (ω.1 (n + (s : ℤ) - 1 + 1))) =
      standardGaussianInfinitePi.map (mainCubeQ3Series n b L) := by
    simpa [b, L] using
      (main_actual_fresh_cube_factor_law n M h hM (n + (s : ℤ) - 1))
  have hcanonical : standardGaussianInfinitePi.map
      (mainCubeQ3Series n b L) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
    calc
      _ = (Cutoff.cutoffSampleLaw M).toMeasure.map
          (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K
            (ω.1 (n + (s : ℤ) - 1 + 1))) := hsource.symm
      _ = (Cutoff.cutoffSampleLaw M).toMeasure.map
          (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K
            (ω.1 (n + (s : ℤ)))) := by
              congr 1
              funext ω
              simp [htime]
      _ = standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := hactual
  have htrace := source_q3_covariance_trace_eq_of_fresh_law
    n M h hM s σ hσ T v hA hlaw x
  let d := fderiv ℝ Φ x
  let Bform : C(K, ℝ) →L[ℝ] C(K, ℝ) →L[ℝ] ℝ := d.smulRight d
  have hgradTrace := @bilinearTrace_eq_of_law
    (GaussianFactorL2 ℕ) (MainCubeH3 n b L)
    (C(closure (cubeSet (originCube 2 n)), ℝ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    v hA T (mainCubeQ3Directions n b L)
    (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
    hcanonical.symm Bform
  have hgrad : modelGradientSquareTrace Φ (fun j => T (v j)) x =
      modelGradientSquareTrace Φ H x := by
    change (∑' j, d (T (v j)) ^ 2) =
      ∑' j, d (pureFluxMainCubeQ3Directions n b L j) ^ 2
    convert hgradTrace using 1 <;>
      (simp [Bform, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
        pureFluxMainCubeQ3Directions, pow_two] <;> rfl)
  have hcov := source_model_q3_positive_generator_row
    n s hs M.nu σ b M.nu_pos hσ x
  have hcov' : (1 / 2 : ℝ) * modelCovarianceTrace Φ H x ≤
      v₀ * D + (2 * v₀ * κ * B + v₀ * μ * B ^ 2) * (Φ x + 4) := by
    simpa [Q, Φ, H, k, Bmix, Brem, B, ρ, δ, κ, μ, v₀,
      Acoef, D, b, L] using hcov
  have hbracket := source_model_q3_full_bracket_row
    n s M.nu σ b M.nu_pos hσ x
  have hbracket' : modelGradientSquareTrace Φ H x ≤
      4 * v₀ * Φ x * ((1 + κ) * D +
        (κB ^ 2 + κ) * B ^ 2 * (Φ x + 4)) := by
    simpa [Q, Φ, H, k, Bmix, Brem, B, ρ, δ, κ, κB, v₀,
      Acoef, D, b, L] using hbracket
  constructor
  · rw [htrace]
    exact hcov'
  · rw [hgrad]
    exact hbracket'

end ASDExplicitGamma.Native

end
