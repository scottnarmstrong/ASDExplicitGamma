/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.P12Regularized
public import ASDExplicitGamma.Gaussian.SquareDirections
public import ASDExplicitGamma.Main.HeatCarrier
public import ASDExplicitGamma.Main.CubeFactor

/-! Actual Q3-factor heat data for finite-even CIR transport. -/

@[expose] public section

open MeasureTheory Set Filter Homogenization ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Main ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Topology ENNReal

namespace ASDExplicitGamma.AllOrder

/-- The model heat law supplies the positive-shift GA-P12 data for an arbitrary
Hilbert realization of the fresh shell.  In particular, the covariance
directions may be kept in the exact physical Q3 factor. -/
theorem aoCir_p12_regularized_model_heat_data_of_realization
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (Φ : C(K, ℝ) → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (hΦ0 : ∀ x, 0 ≤ Φ x) {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    P12RegularizedHeatData (Cutoff.cutoffSampleLaw M).toMeasure
      (p12ModelObservablePath K m Φ)
      (p12ModelGeneratorPath K m Φ (fun j => T (v j)))
      (p12ModelBracketPath K m Φ (fun j => T (v j))) p ε := by
  have hp0 : 0 < p := by linarith
  let Ψ : C(K, ℝ) → ℝ := fun x => (Φ x + ε) ^ p
  let H : ℕ → C(K, ℝ) := fun j => T (v j)
  have hΨ : HasPolynomiallyBoundedC2Derivatives Ψ :=
    hasPolynomiallyBoundedC2Derivatives_positiveShift_rpow hΦ hΦ0 hε hp0
  have hH : Summable (fun j => ‖H j‖ ^ 2) := summable_sq_norm_gaussianDirections hA T
  have hgenEq (x : C(K, ℝ)) :
      modelPositiveShiftPowerHeatGenerator Φ H p ε x =
        (1 / 2 : ℝ) * modelCovarianceTrace Ψ H x := by
    dsimp [modelPositiveShiftPowerHeatGenerator, H, Ψ]
    rw [modelCovarianceTrace_positiveShift_rpow hA T Φ hΦ hΦ0 hε x]
    ring
  have hgenMeas : Measurable (modelPositiveShiftPowerHeatGenerator Φ H p ε) := by
    have heq : modelPositiveShiftPowerHeatGenerator Φ H p ε =
        fun x => (1 / 2 : ℝ) * modelCovarianceTrace Ψ H x := funext hgenEq
    rw [heq]
    exact measurable_const.mul (measurable_modelCovarianceTrace Ψ hΨ.1 H)
  have hgenGrowth : HasPolynomialGrowth
      (modelPositiveShiftPowerHeatGenerator Φ H p ε) := by
    obtain ⟨C, hC, d, hbound⟩ := polynomial_modelCovarianceTrace H hH Ψ hΨ
    refine ⟨C / 2, div_nonneg hC (by norm_num), d, ?_⟩
    intro x
    rw [hgenEq x, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc
      (1 / 2 : ℝ) * |modelCovarianceTrace Ψ H x| ≤
          (1 / 2 : ℝ) * (C * (1 + ‖x‖) ^ d) :=
        mul_le_mul_of_nonneg_left (hbound x) (by norm_num)
      _ = C / 2 * (1 + ‖x‖) ^ d := by ring
  have hpowInt (t : ℝ) : Integrable
      (fun ω : Cutoff.CutoffSample 2 => Ψ (modelInsertedScalar K m t ω))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    p12_integrable_modelInserted_polynomial K M ell m hK hA T hlaw Ψ
      hΨ.1.continuous.measurable
      (by obtain ⟨_, C, hC, d, hval, _, _⟩ := hΨ; exact ⟨C, hC, d, hval⟩) t
  have hpositive : ∀ t ∈ Icc (0 : ℝ) 1, 0 <
      ∫ ω, (p12ModelObservablePath K m Φ t ω + ε) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    intro t ht
    have hpoint (ω : Cutoff.CutoffSample 2) : ε ^ p ≤
        Ψ (modelInsertedScalar K m t ω) := by
      have hbase : ε ≤ Φ (modelInsertedScalar K m t ω) + ε := by
        linarith [hΦ0 (modelInsertedScalar K m t ω)]
      exact Real.rpow_le_rpow (le_of_lt hε) hbase hp0.le
    have hconst : Integrable (fun _ : Cutoff.CutoffSample 2 => ε ^ p)
        (Cutoff.cutoffSampleLaw M).toMeasure := integrable_const _
    have hmono := integral_mono_ae hconst (hpowInt t) (ae_of_all _ hpoint)
    have hconstInt : (∫ _ : Cutoff.CutoffSample 2, ε ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) = ε ^ p := by simp
    have hresult : ε ^ p ≤ ∫ ω, Ψ (modelInsertedScalar K m t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by linarith [hmono, hconstInt]
    have hstrict : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
    simpa [Ψ, p12ModelObservablePath] using lt_of_lt_of_le hstrict hresult
  have hheatInt : ∀ t ∈ Ioo (0 : ℝ) 1,
      Integrable (fun ω => p * (p12ModelObservablePath K m Φ t ω + ε) ^ (p - 1) *
            p12ModelGeneratorPath K m Φ H t ω +
          (p * (p - 1) / 2) * (p12ModelObservablePath K m Φ t ω + ε) ^ (p - 2) *
            p12ModelBracketPath K m Φ H t ω)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro t ht
    have h := p12_integrable_modelInserted_polynomial K M ell m hK hA T hlaw
      (modelPositiveShiftPowerHeatGenerator Φ H p ε) hgenMeas hgenGrowth t
    simpa [p12ModelObservablePath, p12ModelGeneratorPath, p12ModelBracketPath,
      modelPositiveShiftPowerHeatGenerator, H] using h
  have hbase := main_c1On_modelHeatAverage_of_realization K M ell m hK hA T hlaw Ψ hΨ
  refine ⟨?_, hpositive, ?_, hheatInt⟩
  · change ContinuousOn (fun t => modelHeatAverage K M m Ψ t) (Icc (0 : ℝ) 1)
    exact hbase.1.mono Icc_subset_Ici_self
  · intro t ht
    change HasDerivAt (fun r => modelHeatAverage K M m Ψ r)
      (modelHeatAverage K M m (modelPositiveShiftPowerHeatGenerator Φ H p ε) t) t
    have hder := hbase.2.2.1 t ht.1
    have hderH : HasDerivAt (modelHeatAverage K M m Ψ)
        ((1 / 2 : ℝ) * modelHeatTraceAverage K M m Ψ H t) t := by
      simpa only [H] using hder
    have hgen : modelHeatAverage K M m (modelPositiveShiftPowerHeatGenerator Φ H p ε) =
        fun s => (1 / 2 : ℝ) * modelHeatTraceAverage K M m Ψ H s := by
      funext s
      change (∫ ω, modelPositiveShiftPowerHeatGenerator Φ H p ε
          (modelInsertedScalar K m s ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        (1 / 2 : ℝ) * ∫ ω, modelCovarianceTrace Ψ H
          (modelInsertedScalar K m s ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun ω => hgenEq (modelInsertedScalar K m s ω)
    rw [← congrFun hgen t] at hderH
    exact hderH

end ASDExplicitGamma.AllOrder
