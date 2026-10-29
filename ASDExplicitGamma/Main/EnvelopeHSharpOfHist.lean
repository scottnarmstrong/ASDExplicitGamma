module

public import ASDExplicitGamma.Main.EnvelopeHSharpHist
public import ASDExplicitGamma.Main.DirectionalExpectedOfHist
public import ASDExplicitGamma.Main.DirectionalPhysicalFluxOfHist
public import ASDExplicitGamma.Main.ELinearActualLawOfHist
public import ASDExplicitGamma.Main.ELinearObsCellExpectationOfHist
public import ASDExplicitGamma.Main.ELinearObsCellOfHist
public import ASDExplicitGamma.Main.ELinearObsGPartOfHist
public import ASDExplicitGamma.Main.ELinearObsLPartOfHist
public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslationOfHist
public import ASDExplicitGamma.Main.EOscillationDepthFiveProfileOfHist
public import ASDExplicitGamma.Main.HotCovExpectGOfHist
public import ASDExplicitGamma.Main.HotCovNodeFinalOfHist
public import ASDExplicitGamma.Main.HotEOscillationDepthFiveProfileOfHist
public import ASDExplicitGamma.Main.HotEOscillationNodeOfHist
public import ASDExplicitGamma.Main.HotESourceSquareNodeOfHist
public import ASDExplicitGamma.Main.HotObsLocalRowsOfHist
public import ASDExplicitGamma.Main.HotObsMomentsOfHist
public import ASDExplicitGamma.Main.HotObsSplitOfHist
public import ASDExplicitGamma.Main.HotObsVl2OfHist
public import ASDExplicitGamma.Main.HotPositiveSplitGenericOfHist
public import ASDExplicitGamma.Main.HotRemainderFeedbackNodeOfHist
public import ASDExplicitGamma.Main.HotTrialExpectationsSplitOfHist
public import ASDExplicitGamma.Main.MixedBridgeLocalOfHist
public import ASDExplicitGamma.Main.MultiplierMomentsOfHist

/-! The `*_ofHist` variants instantiated with `Hfun := mainEnvelopeH35 (b²) M.gamma`,
`b² = (amp/σ̄_m)²`; the history hypothesis is discharged by the MA-ENVELOPE-H result. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- `main_source_directional_top_physical_flux_expected_matrix_bound_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_source_directional_top_physical_flux_expected_matrix_bound'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero)
    (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      ∫ ω, mainDirectionalTopPhysicalFluxCovarianceMatrix M m t
        (originCube 2 (m - 5)) ω i j
        ∂(Cutoff.cutoffSampleLaw M).toMeasure
    A 0 1 = 0 ∧ A 1 0 = 0 ∧
      A 0 0 ≤ 2 * mainD * mainM0 ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)) *
        (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t) ∧
      A 1 1 ≤ 2 * mainD * mainM0 ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)) *
        (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t) :=
  main_source_directional_top_physical_flux_expected_matrix_bound_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_le M h hM hgamma m hpast) (M := M) (h := h) (hM := hM) (hgamma := hgamma) (m := m) (hpast := hpast) (t := t) (ht0 := ht0) (ht1 := ht1)

/-- `main_source_directional_top_physical_flux_trace_le_multiplier_product_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_source_directional_top_physical_flux_trace_le_multiplier_product'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero)
    (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainSourceDirectionalTopPhysicalFluxTrace M m t ω ≤
        4 * mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal :=
  main_source_directional_top_physical_flux_trace_le_multiplier_product_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_le M h hM hgamma m hpast) (M := M) (h := h) (hM := hM) (hgamma := hgamma) (m := m) (hpast := hpast) (t := t) (ht0 := ht0) (ht1 := ht1)

/-- `main_e_linear_actual_law_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_e_linear_actual_law'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ)
    (hm : m < N)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ)
    (hobs_pos : 1 ≤ hobs)
    (hobs40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    ∃ Lg : CutoffSample 2 → ℝ, Integrable Lg μ ∧
      (∀ᵐ ω ∂μ, mainELinearObsGroup M (originCube 2 (m + (hobs : ℤ))) (5 + hobs) m t b L ω ≤ Lg ω) ∧
      (∫ ω, Lg ω ∂μ) ≤
        mainLinearError (b ^ 2) ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q +
        (mainFourLoadAG (b ^ 2) ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q -
          2 * mainBe (b ^ 2) q) *
          mainG (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) :=
  main_e_linear_actual_law_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (t := t) (ht := ht) (hobs := hobs) (hobs_pos := hobs_pos) (hobs40 := hobs40)

/-- `main_e_fourload_aggregate_actual_law_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_e_fourload_aggregate_actual_law'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ)
    (hm : m < N)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ)
    (hobs_pos : 1 ≤ hobs)
    (hobs40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let Q := originCube 2 (m + (hobs : ℤ))
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    ∃ Ag : CutoffSample 2 → ℝ, Integrable Ag μ ∧
      (∀ᵐ ω ∂μ, mainEHotBottomCovarianceGroup M Q (5 + hobs) m t b L ω +
          b ^ 2 * (Matrix.trace (coarseBlockMatrix (openCubeSet Q)
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (mainELinearObsCoefficient Q m t ω))).lowerRight - 2) +
          mainELinearObsGAverageTerm M Q (5 + hobs) m t b L ω ≤ Ag ω) ∧
      (∫ ω, Ag ω ∂μ) ≤
        mainFourLoadAG (b ^ 2) ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q *
          mainG (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) :=
  main_e_fourload_aggregate_actual_law_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (t := t) (ht := ht) (hobs := hobs) (hobs_pos := hobs_pos) (hobs40 := hobs40)

/-- `main_e_linear_obs_G_part_expectation_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_e_linear_obs_G_part_expectation'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ)
    (hm : m < N)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ)
    (hobs_pos : 1 ≤ hobs)
    (hobs40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    ∃ Gbar2 : CutoffSample 2 → ℝ, Integrable Gbar2 μ ∧ 0 ≤ᵐ[μ] Gbar2 ∧
      (∀ᵐ ω ∂μ, mainELinearObsGAverageTerm M (originCube 2 (m + (hobs : ℤ))) (5 + hobs)
        m t b L ω ≤ Gbar2 ω) ∧
      (∫ ω, Gbar2 ω ∂μ) ≤
        (mainFourLoadAG (b ^ 2) ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q -
          2 * mainBe (b ^ 2) q) *
        mainG (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) :=
  main_e_linear_obs_G_part_expectation_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (t := t) (ht := ht) (hobs := hobs) (hobs_pos := hobs_pos) (hobs40 := hobs40)

/-- `main_e_linear_obs_L_part_expectation_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_e_linear_obs_L_part_expectation'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ)
    (hm : m < N)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ)
    (hobs_pos : 1 ≤ hobs)
    (hobs40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    ∃ Lbar : CutoffSample 2 → ℝ, Integrable Lbar μ ∧ 0 ≤ᵐ[μ] Lbar ∧
      (∀ᵐ ω ∂μ, mainELinearObsLAverageTerm M (originCube 2 (m + (hobs : ℤ))) (5 + hobs) m t b L ω ≤ Lbar ω) ∧
      (∫ ω, Lbar ω ∂μ) ≤ mainLinearError (b ^ 2) ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))
        (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q :=
  main_e_linear_obs_L_part_expectation_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (t := t) (ht := ht) (hobs := hobs) (hobs_pos := hobs_pos) (hobs40 := hobs40)

/-- `main_e_covariance_node_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_e_covariance_node'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ)
    (hm : m < N)
    (hobs : ℕ)
    (h1 : 1 ≤ hobs)
    (h40 : hobs ≤ 40)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    let xi := mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t
    let R1 := mainR1 (inSourceMeanActual M m 5 t) (modelTraceHeatAverage (m + hobs) M m t)
      ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))
    ∃ G : Cutoff.CutoffSample 2 → ℝ,
      Integrable G μ ∧
      (∀ ω, hotCovAffCarrier (originCube 2 (m + hobs)) (hobs + 5) M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1)) ≤ G ω) ∧
      (∀ (ω : Cutoff.CutoffSample 2) (n : whiteBasisIndex),
        2 * (hotPatchTrialTerms (originCube 2 (m + hobs)) (hobs + 5) M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
            (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1))).mixedPlus n -
          2 * (hotPatchTrialTerms (originCube 2 (m + hobs)) (hobs + 5) M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
            (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1))).mixedMinus n =
          oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5)
            (hotCovAffMode (originCube 2 (m + hobs)) (hobs + 5) M.nu
              (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
              (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1)) n) +
          oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5)
            (hotCovOscMode (originCube 2 (m + hobs)) (hobs + 5) M.nu
              (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
              (hotCovObsCoef M m hobs t ω) b (q3ModelLength (m + 1)) n)) ∧
      (∫ ω, G ω ∂μ) ≤
        (b ^ 2 / 2) * R1 ^ 2 +
        2 * (mainKrem (b ^ 2) * R1 + mainKd (b ^ 2) * mainT0 xi) * mainT0 xi *
          Real.sqrt (b ^ 2 + b ^ 2 * q / 4) +
        Real.sqrt 2 * mainT0 xi * R1 * mainEcov (b ^ 2) q :=
  main_e_covariance_node_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (hobs := hobs) (h1 := h1) (h40 := h40) (t := t) (ht := ht)

/-- `main_hot_e_oscillation_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_hot_e_oscillation'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ)
    (hm : m < N)
    (hobs : ℕ)
    (h1 : 1 ≤ hobs)
    (h40 : hobs ≤ 40)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ)
    (hb : 0 < b) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    let a := inSourceMeanActual M m 5 t
    let f := modelTraceHeatAverage (m + hobs) M m t
    let H := (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)
    (∫ ω, mainHotOscRow M m hobs t b ω ∂μ) ≤
      mainEOscillationSourceProfile
        (mainLoadD (b ^ 2) a f H xi (mainKd (b ^ 2))) H (mainOp (b ^ 2)) (mainOm (b ^ 2)) :=
  main_hot_e_oscillation_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (hobs := hobs) (h1 := h1) (h40 := h40) (t := t) (ht := ht) (b := b) (hb := hb)

/-- `main_hot_e_source_square_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_hot_e_source_square'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ)
    (hm : m < N)
    (hobs : ℕ)
    (h1 : 1 ≤ hobs)
    (h40 : hobs ≤ 40)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    let a := inSourceMeanActual M m 5 t
    let f := modelTraceHeatAverage (m + hobs) M m t
    let H := (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)
    (∫ ω, mainHotSourceSquareRow M m hobs t b ω ∂μ) ≤
      mainLoadZ (b ^ 2) a f H xi (mainKd (b ^ 2)) ^ 2 :=
  main_hot_e_source_square_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (hobs := hobs) (h1 := h1) (h40 := h40) (t := t) (ht := ht) (b := b)

/-- `main_hot_e_remainder_feedback_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_hot_e_remainder_feedback'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ)
    (hm : m < N)
    (hobs : ℕ)
    (h1 : 1 ≤ hobs)
    (h40 : hobs ≤ 40)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    let a := inSourceMeanActual M m 5 t
    let f := modelTraceHeatAverage (m + hobs) M m t
    let H := (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)
    (∫ ω, mainHotFeedbackRow M m hobs t b ω ∂μ) ≤
      2 * mainKd (b ^ 2) * (63 / 50) *
        (Real.sqrt 2 * mainBeta * mainLoadD (b ^ 2) a f H xi (mainKd (b ^ 2)) +
          mainLoadZ (b ^ 2) a f H xi (mainKd (b ^ 2)) * mainRec xi) :=
  main_hot_e_remainder_feedback_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (hobs := hobs) (h1 := h1) (h40 := h40) (t := t) (ht := ht) (b := b)

/-- `mixed_bridge_local_parent_gap_rows_ofHist'` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem mixed_bridge_local_parent_gap_rows'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ)
    (hm : m < N)
    (t : ℝ)
    (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 m) 5) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    let B : Cutoff.CutoffSample 2 → ℝ := mixedGlobalHistoryMax M m t
    let V : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVLocal M m U t
    let G : Cutoff.CutoffSample 2 → ℝ := mixedBridgeGLocal M m U t
    let Vl : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVlLocal M m U t
    let f_U := ∫ ω, rawCubeFourLoadTrace M m U t ω ∂μ
    Integrable (fun ω => V ω ^ 2) μ ∧
    (∫ ω, V ω ^ 2 ∂μ) ≤ xi - mainBetaOld * f_U ∧
    (∀ k : Fin 4,
      Integrable (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ ∧
      (∫ ω, B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ∂μ) ≤
        2 * mainBeta ^ k.val * xi) ∧
    Integrable (fun ω => B ω * G ω ^ 2) μ ∧
    (∫ ω, B ω * G ω ^ 2 ∂μ) ≤ 2 * mainBeta * xi ∧
    Integrable (fun ω => B ω * Vl ω ^ 2) μ ∧
    (∫ ω, B ω * Vl ω ^ 2 ∂μ) ≤
      mainBeta * xi + mainEpsNew * mainD * mainBeta *
        (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t) :=
  mixed_bridge_local_parent_gap_rows_ofHist' (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (t := t) (ht := ht) (U := U) (hU := hU)

/-- `main_multiplier_moments_of_main_envelope_h_ofHist` with `Hfun := mainEnvelopeH35 (b²) M.gamma`. -/
theorem main_multiplier_moments_of_main_envelope_h'
    (M : ABKModel 2)
    (h : ℝ)
    (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero)
    (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ((((∫ ω, mainPartialInsertedMultiplierHistory M m t ω ∂
      (Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainM0 ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)) ∧
    (∫ ω, mainD * mainPartialInsertedMultiplierHistory M m t ω *
      (mainPartialInsertedTraceMaxHistory M m t ω).toReal ∂
        (Cutoff.cutoffSampleLaw M).toMeasure) ≤
      mainD * mainM0 ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)) *
        (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)) ∧
    lpNorm (fun ω => mainPartialInsertedMultiplierHistory M m t ω) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      mainM0 ((mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))) ∧
    MemLp (mainPartialInsertedMultiplierHistory M m t) 2
      (Cutoff.cutoffSampleLaw M).toMeasure) ∧
    0 ≤ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      mainPartialInsertedMultiplierHistory M m t :=
  main_multiplier_moments_of_main_envelope_h_ofHist (Hfun := (fun s => mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_le M h hM hgamma m hpast) (M := M) (h := h) (hM := hM) (hgamma := hgamma) (m := m) (hpast := hpast) (t := t) (ht0 := ht0) (ht1 := ht1)

end

end ASDExplicitGamma.Main
