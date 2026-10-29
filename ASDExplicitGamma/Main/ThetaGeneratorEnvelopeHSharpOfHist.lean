module

public import ASDExplicitGamma.Main.EnvelopeHTheta
public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovExpect
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotFeedbackPathwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationPointwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotESourceSquareNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorMixedBridgeLocalCore
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeHSharpHist
public import ASDExplicitGamma.Main.DirectionalExpectedOfHist
public import ASDExplicitGamma.Main.DirectionalPhysicalFluxOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorELinearActualLawOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsCellExpectationOfHist
public import ASDExplicitGamma.Main.ELinearObsCellOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsGPartOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsLPartOfHist
public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslationOfHist
public import ASDExplicitGamma.Main.EOscillationDepthFiveProfileOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovExpectGOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovNodeFinalOfHist
public import ASDExplicitGamma.Main.HotEOscillationDepthFiveProfileOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsLocalRowsOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsMomentsOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsSplitOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2OfHist
public import ASDExplicitGamma.Main.HotPositiveSplitGenericOfHist
public import ASDExplicitGamma.Main.ThetaGeneratorHotRemainderFeedbackMoments
public import ASDExplicitGamma.Main.ThetaGeneratorHotRemainderFeedbackNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplitOfHist
public import ASDExplicitGamma.Main.MultiplierMomentsOfHist

/-! The `*_ofHist` variants instantiated with `Hfun := mainEnvelopeH35Theta (theta M) (b²) M.gamma`,
`b² = (amp/σ̄_m)²`; the history hypothesis is discharged by the MA-ENVELOPE-H result. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- `main_e_linear_actual_law_ofHist_Th` with `Hfun := mainEnvelopeH35Theta (theta M) (b²) M.gamma`. -/
theorem main_e_linear_actual_law_Th
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
        mainLinearError (b ^ 2) ((mainEnvelopeH35Theta (theta M) ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))
          (mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) t) q +
        (mainFourLoadAG (b ^ 2) ((mainEnvelopeH35Theta (theta M) ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))
          (mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) t) q -
          2 * mainBe (b ^ 2) q) *
          mainG (mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) t) :=
  main_e_linear_actual_law_ofHist_Th (Hfun := (fun s => mainEnvelopeH35Theta (theta M) ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N_Th M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (t := t) (ht := ht) (hobs := hobs) (hobs_pos := hobs_pos) (hobs40 := hobs40)

/-- `main_e_covariance_node_ofHist_Th` with `Hfun := mainEnvelopeH35Theta (theta M) (b²) M.gamma`. -/
theorem main_e_covariance_node_Th
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
    let xi := mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    let R1 := mainR1 (inSourceMeanActual M m 5 t) (modelTraceHeatAverage (m + hobs) M m t)
      ((mainEnvelopeH35Theta (theta M) ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t))
    ∃ G : Cutoff.CutoffSample 2 → ℝ,
      Integrable G μ ∧
      (∀ ω, hotCovAffCarrier (originCube 2 (m + hobs)) (hobs + 5) M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (hotCovObsCoef_Th M m hobs t ω) b (q3ModelLength (m + 1)) ≤ G ω) ∧
      (∀ (ω : Cutoff.CutoffSample 2) (n : whiteBasisIndex),
        2 * (hotPatchTrialTerms (originCube 2 (m + hobs)) (hobs + 5) M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
            (hotCovObsCoef_Th M m hobs t ω) b (q3ModelLength (m + 1))).mixedPlus n -
          2 * (hotPatchTrialTerms (originCube 2 (m + hobs)) (hobs + 5) M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
            (hotCovObsCoef_Th M m hobs t ω) b (q3ModelLength (m + 1))).mixedMinus n =
          oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5)
            (hotCovAffMode (originCube 2 (m + hobs)) (hobs + 5) M.nu
              (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
              (hotCovObsCoef_Th M m hobs t ω) b (q3ModelLength (m + 1)) n) +
          oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5)
            (hotCovOscMode (originCube 2 (m + hobs)) (hobs + 5) M.nu
              (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
              (hotCovObsCoef_Th M m hobs t ω) b (q3ModelLength (m + 1)) n)) ∧
      (∫ ω, G ω ∂μ) ≤
        (b ^ 2 / 2) * R1 ^ 2 +
        2 * (mainKrem (b ^ 2) * R1 + mainKd (b ^ 2) * mainT0 xi) * mainT0 xi *
          Real.sqrt (b ^ 2 + b ^ 2 * q / 4) +
        Real.sqrt 2 * mainT0 xi * R1 * mainEcov (b ^ 2) q :=
  main_e_covariance_node_ofHist_Th (Hfun := (fun s => mainEnvelopeH35Theta (theta M) ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s)) (hHist := hot_hist_N_Th M h hM hγ N hpast m hm) (M := M) (h := h) (hM := hM) (hγ := hγ) (N := N) (hpast := hpast) (m := m) (hm := hm) (hobs := hobs) (h1 := h1) (h40 := h40) (t := t) (ht := ht)

end

end ASDExplicitGamma.Main
