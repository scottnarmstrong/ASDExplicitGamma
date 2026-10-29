module

public import ASDExplicitGamma.Main.HotGeneratorPathwise
public import ASDExplicitGamma.Main.Q3HeatIdentity
public import ASDExplicitGamma.Inverse.BankHeatIntegrability

/-! Generator assembly, step 3: the trace identification
`½ · modelHeatTraceAverage = ∫ ½ · (covariance trace at the inserted scalar)` and the
integrability of that integrand on the observer root. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Native
open Algsuperdiff.Section3

noncomputable section

/-- The half covariance trace of the trace defect at the inserted scalar is integrable, and its
integral is the half model heat trace average (the derivative of the observer mean). -/
theorem hot_generator_trace_average (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (n : ℤ) (t : ℝ) :
    let K := closure (cubeSet (originCube 2 n))
    let σ : ℝ := Annealed.sigmaBar M m
    let b := q3ModelAmplitude M h (m + 1)
    let L := q3ModelLength (m + 1)
    let Ψ : C(K, ℝ) → ℝ := modelCovarianceTrace (modelTraceObservable n M.nu σ)
      (pureFluxMainCubeQ3Directions n b L)
    Integrable (fun ω => (1 / 2 : ℝ) * Ψ (modelInsertedScalar K m t ω))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (1 / 2 : ℝ) * modelHeatTraceAverage K M m (modelTraceObservable n M.nu σ)
      (fun j => mainCubeH3Value n b L (mainCubeQ3Directions n b L j)) t =
      ∫ ω, (1 / 2 : ℝ) * Ψ (modelInsertedScalar K m t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  intro K σ b L Ψ
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let H : ℕ → C(K, ℝ) := pureFluxMainCubeQ3Directions n b L
  have hΦ : HasPolynomiallyBoundedC2Derivatives (modelTraceObservable n M.nu σ) :=
    modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu _ M.nu_pos
      (Annealed.sigmaBar M m).2
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(K, ℝ) inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L)
      (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
  have hΨmeas : Measurable Ψ :=
    measurable_modelCovarianceTrace (modelTraceObservable n M.nu σ) hΦ.1 H
  have hΨgrowth : HasPolynomialGrowth Ψ :=
    polynomial_modelCovarianceTrace H hH (modelTraceObservable n M.nu σ) hΦ
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hint : Integrable (fun ω => Ψ (modelInsertedScalar K m t ω))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    bank_model_heat_integrable K M h hM ell m hK Ψ hΨmeas hΨgrowth t
  refine ⟨hint.const_mul (1 / 2 : ℝ), ?_⟩
  unfold modelHeatTraceAverage modelHeatAverage Ψ
  rw [← integral_const_mul]
  rfl

end

end ASDExplicitGamma.Main
