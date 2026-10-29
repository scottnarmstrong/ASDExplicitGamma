module

public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.ThetaGeneratorAffineActualTrace
public import ASDExplicitGamma.Main.AffineFlatBoundary
public import ASDExplicitGamma.Main.AffineFlatLoss
public import ASDExplicitGamma.Main.AffineInverseTrace
public import ASDExplicitGamma.Main.AffineLowerRightMean
public import ASDExplicitGamma.Main.AffineObserverExpectation
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Main.AffineTranslation
public import ASDExplicitGamma.Main.AffineScalarReduction
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeASlope
public import ASDExplicitGamma.Main.EnvelopeSigns
public import ASDExplicitGamma.Native.OldSignedQ1WeakEnvelope
public import ASDExplicitGamma.Native.OldSignedAffineScalarCarrier
public import ASDExplicitGamma.Native.OldSignedAffineTraceMeans
public import ASDExplicitGamma.Native.OldSignedSourceCellFrame
public import ASDExplicitGamma.Native.OldSignedFlatVariancePartition
public import ASDExplicitGamma.Native.OldSignedFlatProfileCaps

import Mathlib.Tactic

/-! Stationary affine estimate in the deterministic OLD response
frame. This file first isolates the exact flat-boundary cap input;
the theorem will discharge it with the actual-law adapter. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  Algsuperdiff.Section3
open scoped ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- The OLD-frame MA-AFFINE assembly on the approved observer cube. Its only
in-node input is the exact q-profile flat-boundary cap. The
rooted carrier, source trace, inverse trace, and square-Poincaré loss are all
the actual source objects at observer depth `hobs + 5`. -/
theorem main_affine_actual_law_of_flat_cap_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hobs : ℕ) (qCap : ℝ)
    (hqCap : qCap ≤ 2)
    (hflatCap : oldSignedFlatBoundaryEnergy
      (originCube 2 (m + (hobs : ℤ)))
      (q3ModelAmplitude M h (m + 1) /
        (Annealed.sigmaBar M m : ℝ))
      (q3ModelLength (m + 1)) ≤
        (q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2 * qCap) :
    let Qobs : TriadicCube 2 := originCube 2 (m + (hobs : ℤ))
    let b := q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)
    (∫ ω, oldSignedFlatAffineContribution Qobs (hobs + 5)
      (oldSignedPartialFrameFieldAt M Qobs m t ω) b
      (q3ModelLength (m + 1))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (b ^ 2 / 2) * mainEnvelopeA (b ^ 2) M.gamma (theta M * mainSourceMeanPrefix) t +
        (b ^ 2 * qCap) * (mainBeta - 1) +
        (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 (b ^ 2) / 9 := by
  dsimp only
  let Q : TriadicCube 2 := originCube 2 (m + (hobs : ℤ))
  let U : TriadicCube 2 := originCube 2 (m - 5)
  let b : ℝ := q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)
  let L := q3ModelLength (m + 1)
  let v : ℝ := b ^ 2
  let Bflat : ℝ := oldSignedFlatBoundaryEnergy Q b L
  let B0 : ℝ := b ^ 2 * qCap
  let beta : ℝ := mainBeta
  let a : ℝ := mainEnvelopeA (b ^ 2) M.gamma (theta M * mainSourceMeanPrefix) t
  let T : ℝ := ∫ ω, traceDefect (cubeSet U)
    (Model.partialInsertedCoefficient M m t ω).toFun
    (Annealed.sigmaBar M m : ℝ) ∂(Cutoff.cutoffSampleLaw M).toMeasure
  let trD : ℝ := 2 * parentBoundaryBandBlockMean M m 1 t U false
  let pBlock : ℝ := parentBoundaryBandBlockMean M m 1 t U true - 1
  let qBlock : ℝ := parentBoundaryBandBlockMean M m 1 t U false - 1
  let x2 : ℝ := oldSignedFlatL2Size Q Q b L true ^ 2
  let y2 : ℝ := oldSignedFlatL2Size Q Q b L false ^ 2
  let X : ℝ := descendantsAverage Q (hobs + 5)
    (fun V => oldSignedFlatMeanSize Q V b L true ^ 2)
  let Y : ℝ := descendantsAverage Q (hobs + 5)
    (fun V => oldSignedFlatMeanSize Q V b L false ^ 2)
  let deltaPlus : ℝ := oldSignedFlatMeanLoss Q (hobs + 5) b L true
  let deltaMinus : ℝ := oldSignedFlatMeanLoss Q (hobs + 5) b L false
  let Aff : ℝ := ∫ ω, oldSignedFlatAffineContribution Q (hobs + 5)
    (oldSignedPartialFrameFieldAt M Q m t ω) b L
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  let A2 : ℝ := mainA2 (b ^ 2)

  have hUsource : U ∈ descendantsAtDepth (originCube 2 m) 5 :=
    originCube_mem_descendantsAtDepth' 2 m 5
  have hUscale : U.scale = m - 5 := by
    simp only [U, originCube]
  have hUobserverScale : U ∈ descendantsAtScale Q (m - 5) :=
    Algsuperdiff.Section3.Provider.ErrorComparison.originCube_mem_descendantsAtScale
      (d := 2) (by omega)
  have hobserverDepth : Int.toNat (Q.scale - (m - 5)) = hobs + 5 := by
    simp only [Q, originCube]
    omega
  have hUobserverScaleDepth : U ∈ descendantsAtDepth Q
      (Int.toNat (Q.scale - (m - 5))) := by
    rw [← descendantsAtScale_eq_descendantsAtDepth Q (by
      simp only [Q, originCube]
      omega)]
    exact hUobserverScale
  have hUobserver : U ∈ descendantsAtDepth Q (hobs + 5) := by
    rw [← hobserverDepth]
    exact hUobserverScaleDepth

  have ht' : 0 ≤ t ∧ t ≤ 1 := ⟨ht.1, ht.2⟩
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) :=
    (Annealed.sigmaBar_characterization M m).1

  have hTactual : T = mainMeanActual_Th M m t := by
    dsimp [T, U]
    exact main_affine_actual_trace_mean_Th M h hM m t ht'
  have hEnvelope := main_envelope_a_actual_law_Th M h hM hγ N hpast m hm ht
  have hTle : T ≤ a := by
    calc
      T = mainMeanActual_Th M m t := hTactual
      _ ≤ mainEnvelopeA
          ((q3ModelAmplitude M h (m + 1)) ^ 2 /
            (Annealed.sigmaBar M m : ℝ) ^ 2)
          M.gamma (theta M * mainSourceMeanPrefix) t := hEnvelope
      _ = a := by
        dsimp [a, b]
        congr 2
        field_simp [hσ.ne']
  have ha : 0 ≤ a := by
    dsimp [a]
    have ha0 : 0 ≤ theta M * mainSourceMeanPrefix := by
      have hθ0 : 0 ≤ theta M := by
        unfold theta
        exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
      have := mainSourceMeanPrefix_gate
      positivity
    exact ha0.trans
      (mainEnvelopeA_ge_initial (sq_nonneg b)
        M.shellPrefix.gamma_pos.le ht.1)

  have hpmean := parent_boundary_band_block_mean
    M h hM m 1 (by norm_num) 5 U hUsource t true
  have hqmean := parent_boundary_band_block_mean
    M h hM m 1 (by norm_num) 5 U hUsource t false
  have hp : -1 ≤ pBlock := by dsimp [pBlock]; linarith [hpmean.1]
  have hq : -1 ≤ qBlock := by dsimp [qBlock]; linarith [hqmean.1]

  have hsource := old_signed_q1_source_mean_eq M m U hUscale t ht' 0
  simp only [Nat.add_zero] at hsource
  have hblockTrace := old_signed_affine_block_trace_mean
    M h hM m 5 U hUsource t ht'
  have hTidentity : T = 2 * (pBlock + qBlock) := by
    calc
      T = mainMeanActual_Th M m t := hTactual
      _ = inSourceMeanActual M m 5 t := rfl
      _ = ∫ ω, rawWeakTraceSequence M m U t ω 0
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := hsource.symm
      _ = 2 * (pBlock + qBlock) := by
            simpa [pBlock, qBlock] using hblockTrace

  have hLowerMean := main_affine_lower_right_trace_mean M h hM m t
  have hpoint (ω : Cutoff.CutoffSample 2) :
      Matrix.trace (coarseBlockMatrix (cubeSet U)
        (oldSignedPartialFrameField M m 1 t ω)).lowerRight =
      (Annealed.sigmaBar M m : ℝ) * Matrix.trace
        (coarseBlockMatrix (cubeSet U)
          (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight := by
    rw [old_signed_partial_cell_frame M m 1 t ω U 5 hUsource]
    simp [Variational.frameMatrix, Matrix.trace_smul]
  have hpointRoot (ω : Cutoff.CutoffSample 2) :
      Matrix.trace (coarseBlockMatrix (cubeSet U)
        (oldSignedPartialFrameFieldAt M Q m t ω)).lowerRight =
      (Annealed.sigmaBar M m : ℝ) * Matrix.trace
        (coarseBlockMatrix (cubeSet U)
          (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight := by
    rw [old_signed_partial_cell_frame_at M Q m t ω U (hobs + 5) hUobserver]
    simp [Variational.frameMatrix, Matrix.trace_smul]
  have hpointTransfer (ω : Cutoff.CutoffSample 2) :
      Matrix.trace (coarseBlockMatrix (cubeSet U)
        (oldSignedPartialFrameField M m 1 t ω)).lowerRight =
      Matrix.trace (coarseBlockMatrix (cubeSet U)
        (oldSignedPartialFrameFieldAt M Q m t ω)).lowerRight := by
    calc
      _ = (Annealed.sigmaBar M m : ℝ) * Matrix.trace
          (coarseBlockMatrix (cubeSet U)
            (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight := hpoint ω
      _ = _ := hpointRoot ω |>.symm
  have hsourceFrameInt :
      (∫ ω, Matrix.trace (coarseBlockMatrix (cubeSet U)
          (oldSignedPartialFrameField M m 1 t ω)).lowerRight
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫ ω, Matrix.trace (coarseBlockMatrix (cubeSet U)
          (oldSignedPartialFrameFieldAt M Q m t ω)).lowerRight
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpointTransfer
  have hObserverCap := main_affine_inverse_trace_frame_cells
    M h hM hγ N hpast m hm t ht hobs U hUobserver
  have hrootFrameInt :
      (∫ ω, Matrix.trace (coarseBlockMatrix (cubeSet U)
          (oldSignedPartialFrameFieldAt M Q m t ω)).lowerRight
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫ ω, (Annealed.sigmaBar M m : ℝ) * Matrix.trace
          (coarseBlockMatrix (cubeSet U)
            (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpointRoot
  have htrDle : trD ≤ 2 * mainBeta := by
    dsimp [trD, U] at hLowerMean ⊢
    calc
      2 * parentBoundaryBandBlockMean M m 1 t (originCube 2 (m - 5)) false =
          ∫ ω, Matrix.trace (coarseBlockMatrix
            (cubeSet (originCube 2 (m - 5)))
            (oldSignedPartialFrameField M m 1 t ω)).lowerRight
            ∂(Cutoff.cutoffSampleLaw M).toMeasure := hLowerMean.symm
      _ = ∫ ω, Matrix.trace (coarseBlockMatrix (cubeSet U)
            (oldSignedPartialFrameFieldAt M Q m t ω)).lowerRight
            ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
              simpa [U] using hsourceFrameInt
      _ = ∫ ω, (Annealed.sigmaBar M m : ℝ) * Matrix.trace
            (coarseBlockMatrix (cubeSet U)
              (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight
            ∂(Cutoff.cutoffSampleLaw M).toMeasure := hrootFrameInt
      _ ≤ 2 * mainBeta := hObserverCap
  have htrIdentity : trD = 2 + 2 * qBlock := by
    dsimp [trD, qBlock]
    ring

  have hBflat : Bflat ≤ B0 := by
    simpa [Bflat, B0, Q, b, L] using hflatCap
  have hflatBounds := old_signed_flat_boundary_energy_bounds Q b L
  have hB : 0 ≤ Bflat := by simpa [Bflat] using hflatBounds.1
  have hB0 : Bflat ≤ B0 := hBflat
  have hBcap : B0 ≤ 2 * v := by
    dsimp [B0, v]
    calc
      b ^ 2 * qCap ≤ b ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hqCap (sq_nonneg b)
      _ = 2 * b ^ 2 := by ring
  have hbeta : 1 ≤ beta := by norm_num [beta, mainBeta]

  have hxsum : x2 + y2 = 2 * v := by
    dsimp [x2, y2, v]
    exact old_signed_joint_flat_l2_identity Q b L
  have hxdiff : x2 - y2 = Bflat := by
    dsimp [x2, y2, Bflat]
    exact old_signed_flat_l2_difference Q b L
  have hX : X = x2 - deltaPlus := by
    dsimp [X, x2, deltaPlus]
    exact old_signed_flat_mean_partition_identity Q (hobs + 5) b L true
  have hY : Y = y2 - deltaMinus := by
    dsimp [Y, y2, deltaMinus]
    exact old_signed_flat_mean_partition_identity Q (hobs + 5) b L false
  have hdeltaPlus : 0 ≤ deltaPlus := by
    dsimp [deltaPlus]
    exact old_signed_flat_mean_loss_nonneg Q (hobs + 5) b L true
  have hdeltaMinus : 0 ≤ deltaMinus := by
    dsimp [deltaMinus]
    exact old_signed_flat_mean_loss_nonneg Q (hobs + 5) b L false
  have hdeltaCap := main_affine_flat_mean_loss_pair_cap_observer M h m hobs
  have hdelta : deltaPlus + deltaMinus ≤
      (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * A2 / 9 := by
    simpa [deltaPlus, deltaMinus, A2, Q, b, L] using hdeltaCap
  have hAffIdentity : Aff = qBlock * X + pBlock * Y := by
    dsimp [Aff, qBlock, X, pBlock, Y, Q]
    exact main_affine_observer_affine_identity M h hM m hobs t b L

  have hred := main_affine_scalar_reduction
    v Bflat B0 beta a T trD pBlock qBlock x2 y2 X Y deltaPlus deltaMinus Aff A2
    hB hB0 hBcap hbeta ha hTle htrDle hp hq hTidentity htrIdentity
    hxsum hxdiff hX hY hdeltaPlus hdeltaMinus hAffIdentity hdelta
  simpa [Aff, v, B0, beta, a, A2, b, Q, U, L] using hred

private theorem main_affine_flat_boundary_cap_profile_le_two (d : ℕ) :
    mainAffineFlatBoundaryCapQ d ≤ 2 := by
  by_cases h0 : d = 0
  · subst d
    norm_num [mainAffineFlatBoundaryCapQ]
  by_cases h1 : d = 1
  · subst d
    norm_num [mainAffineFlatBoundaryCapQ]
  by_cases h2 : d = 2
  · subst d
    norm_num [mainAffineFlatBoundaryCapQ]
  by_cases h3 : d = 3
  · subst d
    norm_num [mainAffineFlatBoundaryCapQ]
  by_cases h4 : d = 4
  · subst d
    norm_num [mainAffineFlatBoundaryCapQ]
  by_cases h5 : d = 5
  · subst d
    norm_num [mainAffineFlatBoundaryCapQ]
  · have hd : 6 ≤ d := by omega
    have hpow : (3 : ℕ) ^ 6 ≤ 3 ^ d :=
      pow_le_pow_right' (by norm_num : 1 ≤ (3 : ℕ)) hd
    have hpowR : (3 : ℝ) ^ 6 ≤ 3 ^ d := by exact_mod_cast hpow
    have hmode_eq :
        (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) =
          1 / (3 : ℝ) ^ d := by
      simp [ASDExplicitGamma.Numerics.Model.q3ModeLength]
    have hmode :
        (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) ≤ 1 / 729 := by
      rw [hmode_eq]
      calc
        (1 : ℝ) / 3 ^ d ≤ 1 / (3 : ℝ) ^ 6 :=
          one_div_le_one_div_of_le (by positivity) hpowR
        _ = 1 / 729 := by norm_num
    have hmode_nonneg :
        0 ≤ (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) := by
      rw [hmode_eq]
      positivity
    have htail :
        (429 / 175 : ℝ) *
            (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) -
          (7 / 15 : ℝ) *
            (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg
        (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ)]
    simpa [mainAffineFlatBoundaryCapQ, h0, h1, h2, h3, h4, h5] using htail

/-- The MA-AFFINE estimate on the approved observer cube,
with the exact q-profile cap and no cap premise. -/
theorem main_affine_actual_law_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (hobs1 : 1 ≤ hobs) (hobs40 : hobs ≤ 40) :
    let Qobs : TriadicCube 2 := originCube 2 (m + (hobs : ℤ))
    let b := q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)
    (∫ ω, oldSignedFlatAffineContribution Qobs (hobs + 5)
      (oldSignedPartialFrameFieldAt M Qobs m t ω) b
      (q3ModelLength (m + 1))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (b ^ 2 / 2) * mainEnvelopeA (b ^ 2) M.gamma (theta M * mainSourceMeanPrefix) t +
        (b ^ 2 * mainAffineFlatBoundaryCapQ (hobs - 1)) *
          (mainBeta - 1) +
        (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 (b ^ 2) / 9 := by
  have hflatCap := main_affine_flat_boundary_cap
    M h hM m hobs hobs1 hobs40
  exact main_affine_actual_law_of_flat_cap_Th
    M h hM hγ N hpast m hm ht hobs
    (mainAffineFlatBoundaryCapQ (hobs - 1))
    (main_affine_flat_boundary_cap_profile_le_two (hobs - 1)) hflatCap

end
end ASDExplicitGamma.Main

end
