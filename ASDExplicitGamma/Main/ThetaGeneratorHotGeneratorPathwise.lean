module

public import ASDExplicitGamma.Main.ThetaGeneratorHotCovExpect
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotFeedbackPathwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationPointwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationPathwise
public import ASDExplicitGamma.Main.HotGeneratorSeries
public import ASDExplicitGamma.Native.OldSignedModelTraceBridge
public import ASDExplicitGamma.Native.OldSignedPhysicalTraceSeries
public import ASDExplicitGamma.Main.HotPatchTrial
public import ASDExplicitGamma.Main.ThetaGeneratorHotESourceSquareNode
public import ASDExplicitGamma.Main.HotBottomCovariancePathwise

/-! Generator assembly, step 2: the pathwise bound of the half covariance trace of the
trace defect on the observer root by the grouped hot-trial rows. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational ASDExplicitGamma.Model
open Algsuperdiff.Section3

noncomputable section

/-- Pathwise generator bound at the observer root: half the covariance trace of the trace
defect at the actual inserted scalar is at most the sum of the grouped hot-trial rows. -/
theorem hot_generator_pathwise_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t b : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    let σ : ℝ := Annealed.sigmaBar M m
    let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
    let L := q3ModelLength (m + 1)
    let Q := originCube 2 (m + (hobs : ℤ))
    let k := mainELinearObsCoefficient Q m t ω
    (1 / 2 : ℝ) * modelCovarianceTrace (modelTraceObservable (m + (hobs : ℤ)) M.nu σ)
      (pureFluxMainCubeQ3Directions (m + (hobs : ℤ)) (σ * b) L)
      (modelInsertedScalar (closure (cubeSet Q)) m t ω) ≤
    mainELinearObsGroup M Q (5 + hobs) m t b L ω +
      oldSignedFlatBoundaryEnergy Q b L +
      oldSignedFlatAffineContribution Q (hobs + 5)
        (responseFramePlanarCoefficientField M.nu σ k) b L +
      mainHotSourceSquareRow_Th M m hobs t b ω +
      hotCovAffCarrier Q (hobs + 5) M.nu σ M.nu_pos hσ (hotCovObsCoef_Th M m hobs t ω) b L +
      mainHotOscRow_Th M m hobs t b ω +
      mainHotFeedbackRow_Th M m hobs t b ω +
      mainEHotTopCovarianceGroup M Q (5 + hobs) m t b L ω +
      mainEHotBottomCovarianceGroup M Q (5 + hobs) m t b L ω := by
  classical
  intro σ hσ L Q k
  have h5 : 5 + hobs = hobs + 5 := Nat.add_comm _ _
  rw [old_signed_model_trace_generator_eq (m + (hobs : ℤ)) M.nu σ M.nu_pos hσ b L]
  have hk : pureFluxOpenResponseRestriction (m + (hobs : ℤ))
      (modelInsertedScalar (closure (cubeSet Q)) m t ω) = k := rfl
  rw [hk]
  have hser := hot_trial_total_hasSum (m + (hobs : ℤ)) (hobs + 5) M.nu σ M.nu_pos hσ k b L
    (hotCov_hL_obs_Th m hobs) (hotCov_hmesh_obs_Th m hobs)
  have hle : (∑' n : whiteBasisIndex, ∑ c : BlockCoord 2,
      oldSignedPhysicalHessian Q M.nu σ M.nu_pos hσ k (blockBasis c) b L n) ≤
      ∑' n, (hotPatchTrialTerms Q (hobs + 5) M.nu σ M.nu_pos hσ k b L).total n :=
    Summable.tsum_le_tsum (fun n => hot_patch_canonical_hessian_le_trial_total Q (hobs + 5) M.nu σ
      M.nu_pos hσ k b L n)
      (old_signed_physical_trace_summable (m + (hobs : ℤ)) M.nu σ M.nu_pos hσ k b L)
      hser.summable
  refine hle.trans ?_
  rw [hser.tsum_eq]
  have hosc : (∑' n, oldSignedCellAverage Q (hobs + 5)
      (hotCovOscMode Q (hobs + 5) M.nu σ M.nu_pos hσ k b L n)) ≤
      mainHotOscRow_Th M m hobs t b ω := by
    have hs := old_signed_cell_average_series Q (hobs + 5)
      (fun n U => hotCovOscMode Q (hobs + 5) M.nu σ M.nu_pos hσ k b L n U)
      (fun U => hotGen_osc_cell_summable (m + (hobs : ℤ)) (hobs + 5) M.nu σ M.nu_pos hσ k b L
        (hotCov_hL_obs_Th m hobs) U)
    rw [hs.2]
    unfold mainHotOscRow_Th hotOscRow_Th
    rw [← old_signed_cell_average_eq_descendantsAverage]
    apply old_signed_cell_average_mono
    intro U
    rw [dif_pos U.property]
    exact le_abs_self _
  have hLg : mainELinearObsGroup M Q (5 + hobs) m t b L ω =
      ∑' n, ((hotPatchTrialTerms Q (hobs + 5) M.nu σ M.nu_pos hσ k b L).flat n -
        oldSignedFlatBoundaryModeEnergy Q b L n -
        oldSignedFlatAffineMode Q (hobs + 5) (responseFramePlanarCoefficientField M.nu σ k) b L n +
        2 * (hotPatchTrialTerms Q (hobs + 5) M.nu σ M.nu_pos hσ k b L).feedbackPlus n -
        2 * (hotPatchTrialTerms Q (hobs + 5) M.nu σ M.nu_pos hσ k b L).feedbackMinus n) := by
    rw [h5]; rfl
  rw [hLg]
  have hTop : mainEHotTopCovarianceGroup M Q (5 + hobs) m t b L ω =
      ∑' n, (hotPatchTrialTerms Q (hobs + 5) M.nu σ M.nu_pos hσ k b L).covarianceTop n := by
    rw [h5]; rfl
  have hBot : mainEHotBottomCovarianceGroup M Q (5 + hobs) m t b L ω =
      ∑' n, (hotPatchTrialTerms Q (hobs + 5) M.nu σ M.nu_pos hσ k b L).covarianceBottom n := by
    rw [h5]; rfl
  rw [hTop, hBot]
  have hSrc : mainHotSourceSquareRow_Th M m hobs t b ω =
      ∑' n, (hotPatchTrialTerms Q (hobs + 5) M.nu σ M.nu_pos hσ k b L).source n := rfl
  have hFb : mainHotFeedbackRow_Th M m hobs t b ω =
      2 * ∑' n, (hotPatchTrialTerms Q (hobs + 5) M.nu σ M.nu_pos hσ k b L).feedbackSource n := rfl
  rw [hSrc, hFb]
  have hBe : oldSignedFlatBoundaryEnergy Q b L = ∑' n, oldSignedFlatBoundaryModeEnergy Q b L n := rfl
  have hAf : oldSignedFlatAffineContribution Q (hobs + 5)
      (responseFramePlanarCoefficientField M.nu σ k) b L =
      ∑' n, oldSignedFlatAffineMode Q (hobs + 5) (responseFramePlanarCoefficientField M.nu σ k) b L n := rfl
  rw [hBe, hAf]
  have hcoef : hotCovObsCoef_Th M m hobs t ω = k := rfl
  rw [hcoef]
  linarith [hosc]

end

end ASDExplicitGamma.Main
