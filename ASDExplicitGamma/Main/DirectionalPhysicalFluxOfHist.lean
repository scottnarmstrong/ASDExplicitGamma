module

public import ASDExplicitGamma.Main.DirectionalPhysicalFlux

/-! Successors of `DirectionalPhysicalFlux` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Inverse
  ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped RealInnerProductSpace

noncomputable section

/-- Successor of `main_source_directional_top_physical_flux_trace_le_multiplier_product` with the history envelope `Hfun`. -/
theorem main_source_directional_top_physical_flux_trace_le_multiplier_product_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainSourceDirectionalTopPhysicalFluxTrace M m t ω ≤
        4 * mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by
  have hEnvelope := hHist t ⟨ht0, ht1⟩
  have hfinite : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainPartialInsertedTraceMaxHistory M m t ω < ⊤ := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.1
  filter_upwards [hfinite] with ω hω
  have htrace := main_directional_top_physical_flux_trace_le_corrector_history
    M m t (originCube 2 (m - 5)) ω
  have hcorrector := main_directional_corrector_history_le_multiplier_product
    M m t ⟨ht0, ht1⟩ ω hω
  calc
    mainSourceDirectionalTopPhysicalFluxTrace M m t ω ≤
        4 * oldSignedCorrectorHistory (originCube 2 (m - 5))
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) := by
      simpa [mainSourceDirectionalTopPhysicalFluxTrace] using
        main_directional_top_physical_flux_trace_le_corrector_history
          M m t (originCube 2 (m - 5)) ω
    _ ≤ 4 * (mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal) :=
      mul_le_mul_of_nonneg_left hcorrector (by norm_num)
    _ = 4 * mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by ring

/-- Successor of `main_source_directional_top_physical_flux_covariance_trace_le_multiplier_product` with the history envelope `Hfun`. -/
theorem main_source_directional_top_physical_flux_covariance_trace_le_multiplier_product_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Matrix.trace (mainDirectionalTopPhysicalFluxCovarianceMatrix M m t
        (originCube 2 (m - 5)) ω) ≤
        4 * mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by
  have htrace := main_source_directional_top_physical_flux_trace_le_multiplier_product_ofHist (Hfun := Hfun) (hHist := hHist)
    M h hM hgamma m hpast t ht0 ht1
  filter_upwards [htrace] with ω hω
  rw [← main_directional_top_physical_flux_trace_eq_covariance_matrix_trace
    M m t (originCube 2 (m - 5)) ω]
  exact hω

end
end ASDExplicitGamma.Main
end
