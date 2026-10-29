/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirResetProfiles
public import ASDExplicitGamma.AllOrder.CirFamilyHeatData
public import ASDExplicitGamma.Inverse.FullResponseTrace
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks

/-! # Trace identification for reset-driven CIR shell paths -/

@[expose] public section

open Homogenization MeasureTheory
open Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Variational

namespace ASDExplicitGamma.AllOrder

local instance cirResetTraceParentCompact (n : ℤ) :
    CompactSpace (closure (cubeSet (originCube 2 n))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure

private theorem cir_planarCoefficient_eq_of_symmPart (ν : ℝ) (A : Mat 2)
    (hA : symmPart A = ν • (1 : Mat 2)) :
    responsePlanarCoefficient ν (A 1 0) = A := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  norm_num [symmPart, Matrix.smul_apply, Matrix.one_apply] at h00 h11 h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ] <;> linarith

private theorem cir_symmPart_modelInserted (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    symmPart (Model.partialInsertedCoefficient M m t ω x) = M.nu • (1 : Mat 2) := by
  have ha := Cutoff.symmPart_coefficientCutoff M.nu m ω x
  ext i j
  have hb := congrFun (congrFun ha i) j
  have hj := (ω.1 (m + 1)).skew_entry x i j
  change (Cutoff.coefficientCutoff M.nu m ω x i j +
      Cutoff.coefficientCutoff M.nu m ω x j i) / 2 =
      (M.nu • (1 : Mat 2)) i j at hb
  change ((Cutoff.coefficientCutoff M.nu m ω x i j +
      Real.sqrt t * ω.1 (m + 1) x i j) +
      (Cutoff.coefficientCutoff M.nu m ω x j i +
      Real.sqrt t * ω.1 (m + 1) x j i)) / 2 = _
  rw [hj]
  linarith

/-- The response-frame coefficient on a translated square has the same coarse
matrix as the physical response coefficient viewed in the requested true
frame.  This is the translated-square form of the corresponding origin-square
identity used in the inverse bank adapters. -/
theorem cir_response_coarseMatrix_frame_eq (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    coarseBlockMatrix (cubeSet Q) (responseFramePlanarCoefficientField ν σ k) =
      frameMatrix σ (coarseBlockMatrix (cubeSet Q)
        (responsePlanarCoefficientField ν k)) := by
  let U := cubeSet Q
  let a₁ := responsePlanarCoefficientField 1 (ν⁻¹ • k)
  have ha₁ : responseFramePlanarCoefficientField 1 1 (ν⁻¹ • k) = a₁ := by
    ext x i j
    simp [a₁, responseFramePlanarCoefficientField,
      responsePlanarCoefficientField]
  have hEll₁ : IsEllipticFieldOn 1 (1 + ‖ν⁻¹ • k‖ ^ 2) U a₁ := by
    have h := lemmaV_frameCoefficient_isEllipticOn
      (measurableSet_cubeSet Q) 1 1 (by norm_num) (by norm_num) (ν⁻¹ • k)
    rw [ha₁] at h
    norm_num at h
    exact h
  have hCoeffFrameOn (x : Vec 2) (hx : x ∈ openCubeSet Q) :
      responseFramePlanarCoefficientField ν σ k x =
        ((ν / σ) • responsePlanarCoefficientField 1 (ν⁻¹ • k)) x := by
    unfold responseFramePlanarCoefficientField
    unfold responsePlanarCoefficientField
    change responsePlanarCoefficient (ν / σ)
        (responseCoefficientExtension k x / σ) =
      (ν / σ) • responsePlanarCoefficient 1
        (responseCoefficientExtension (ν⁻¹ • k) x)
    rw [responseCoefficientExtension_smul_on (ν⁻¹) k hx]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [responsePlanarCoefficient, responsePlanarJ, Matrix.smul_apply,
        smul_eq_mul] <;> field_simp [hν.ne', hσ.ne']
  have hCoeffPhysicalOn (x : Vec 2) (hx : x ∈ openCubeSet Q) :
      responsePlanarCoefficientField ν k x =
        (ν • responsePlanarCoefficientField 1 (ν⁻¹ • k)) x := by
    unfold responsePlanarCoefficientField
    change responsePlanarCoefficient ν (responseCoefficientExtension k x) =
      (ν • responsePlanarCoefficientField 1 (ν⁻¹ • k)) x
    unfold responsePlanarCoefficientField
    change responsePlanarCoefficient ν (responseCoefficientExtension k x) =
      ν • responsePlanarCoefficient 1
        (responseCoefficientExtension (ν⁻¹ • k) x)
    rw [responseCoefficientExtension_smul_on (ν⁻¹) k hx]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [responsePlanarCoefficient, responsePlanarJ, Matrix.smul_apply,
        smul_eq_mul] <;> field_simp [hν.ne']
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsν_sq : (Real.sqrt ν) ^ 2 = ν := Real.sq_sqrt hν.le
  have hCoeffPhysical' : ∀ x ∈ openCubeSet Q,
      responsePlanarCoefficientField ν k x = ((Real.sqrt ν) ^ 2 • a₁) x := by
    intro x hx
    rw [hsν_sq]
    simpa only [a₁] using hCoeffPhysicalOn x hx
  have hCoarsePhysical :
      coarseBlockMatrix U (responsePlanarCoefficientField ν k) =
        coarseMatrixRescale (Real.sqrt ν) (coarseBlockMatrix U a₁) := by
    have hAEopen : responsePlanarCoefficientField ν k =ᵐ[volume.restrict (openCubeSet Q)]
        ((Real.sqrt ν) ^ 2 • a₁) := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with x hx
      exact hCoeffPhysical' x hx
    have hAE : responsePlanarCoefficientField ν k =ᵐ[volume.restrict U]
        ((Real.sqrt ν) ^ 2 • a₁) := by
      change responsePlanarCoefficientField ν k =ᵐ[volume.restrict (cubeSet Q)] _
      rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      exact hAEopen
    rw [coarseBlockMatrix_congr_of_ae_eq hAE]
    exact coarseBlockMatrix_sq_smul_triCube hEll₁ hsν
  have hsFrame : 0 < Real.sqrt (ν / σ) :=
    Real.sqrt_pos.2 (div_pos hν hσ)
  have hsFrame_sq : (Real.sqrt (ν / σ)) ^ 2 = ν / σ :=
    Real.sq_sqrt (div_nonneg hν.le hσ.le)
  have hCoeffFrame' : ∀ x ∈ openCubeSet Q,
      responseFramePlanarCoefficientField ν σ k x =
        ((Real.sqrt (ν / σ)) ^ 2 • a₁) x := by
    intro x hx
    rw [hsFrame_sq]
    simpa only [a₁] using hCoeffFrameOn x hx
  have hCoarseFrame :
      coarseBlockMatrix U (responseFramePlanarCoefficientField ν σ k) =
        coarseMatrixRescale (Real.sqrt (ν / σ)) (coarseBlockMatrix U a₁) := by
    have hAEopen : responseFramePlanarCoefficientField ν σ k =ᵐ[volume.restrict (openCubeSet Q)]
        ((Real.sqrt (ν / σ)) ^ 2 • a₁) := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with x hx
      exact hCoeffFrame' x hx
    have hAE : responseFramePlanarCoefficientField ν σ k =ᵐ[volume.restrict U]
        ((Real.sqrt (ν / σ)) ^ 2 • a₁) := by
      change responseFramePlanarCoefficientField ν σ k =ᵐ[volume.restrict (cubeSet Q)] _
      rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      exact hAEopen
    rw [coarseBlockMatrix_congr_of_ae_eq hAE]
    exact coarseBlockMatrix_sq_smul_triCube hEll₁ hsFrame
  have hInvFrame : (Real.sqrt (ν / σ)) ^ (-2 : ℤ) = σ / ν := by
    rw [zpow_neg, zpow_ofNat, hsFrame_sq]
    field_simp [hν.ne', hσ.ne']
  have hInvν : (Real.sqrt ν) ^ (-2 : ℤ) = ν⁻¹ := by
    rw [zpow_neg, zpow_ofNat, hsν_sq]
  have hRescale :
      coarseMatrixRescale (Real.sqrt (ν / σ)) (coarseBlockMatrix U a₁) =
        frameMatrix σ (coarseMatrixRescale (Real.sqrt ν)
          (coarseBlockMatrix U a₁)) := by
    cases coarseBlockMatrix U a₁ with
    | mk ul ur ll lr =>
      have hUL : (Real.sqrt (ν / σ)) ^ 2 • ul =
          σ⁻¹ • ((Real.sqrt ν) ^ 2 • ul) := by
        ext i j
        simp [Matrix.smul_apply, smul_eq_mul, hsFrame_sq, hsν_sq]
        field_simp [hν.ne', hσ.ne']
      have hLR : (Real.sqrt (ν / σ)) ^ (-2 : ℤ) • lr =
          σ • ((Real.sqrt ν) ^ (-2 : ℤ) • lr) := by
        ext i j
        simp [Matrix.smul_apply, smul_eq_mul, hInvFrame, hInvν]
        field_simp [hν.ne', hσ.ne']
      simp only [coarseMatrixRescale, frameMatrix, BlockMat.mk.injEq]
      exact ⟨hUL, trivial, trivial, hLR⟩
  rw [hCoarseFrame, hCoarsePhysical, hRescale]

/-- The full-frame trace root is exactly the translated-square trace
whenever the physical response coefficient agrees almost everywhere with the
attenuated coefficient used by the reset. -/
theorem root_trace_eq_squareTrace_of_ae
    (M : ABKModel 2) (Q : TriadicCube 2) (m N K₀ : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (k : ResponseCoefficient (openCubeSet Q))
    (hcoef : responsePlanarCoefficientField M.nu k =ᵐ[volume.restrict (cubeSet Q)]
      attenuatedCoefficient M m N weights ω) :
    rootTraceObservable M Q m N K₀ weights ω =
      squareTrace Q M.nu (Annealed.sigmaBar M K₀ : ℝ) k + 4 := by
  have hσ : 0 < (Annealed.sigmaBar M K₀ : ℝ) :=
    (Annealed.sigmaBar_characterization M K₀).1
  have hcoarse :
      coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu k) =
        coarseBlockMatrix (cubeSet Q)
          (attenuatedCoefficient M m N weights ω) :=
    coarseBlockMatrix_congr_of_ae_eq hcoef
  have hframe := cir_response_coarseMatrix_frame_eq Q M.nu
    (Annealed.sigmaBar M K₀ : ℝ) M.nu_pos hσ k
  have hg4base : squareTrace Q M.nu (Annealed.sigmaBar M K₀ : ℝ) k =
      Matrix.trace (toFullBlockMat (coarseBlockMatrix (cubeSet Q)
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M K₀ : ℝ) k))) - 4 := by
    unfold Gaussian.squareTrace
    rw [traceDefect_eq_full_framedTrace]
    simp [frameMatrix]
  have hg4 : squareTrace Q M.nu (Annealed.sigmaBar M K₀ : ℝ) k =
      Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M K₀ : ℝ)
        (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField M.nu k)))) - 4 := by
    rw [hg4base, hframe]
  rw [hcoarse] at hg4
  rw [root_trace_observable_eq_trace_defect,
    traceDefect_eq_full_framedTrace, hg4]

/-- The reset inverse root is the operator norm of the normalized response
coarse block in its requested reference frame. -/
theorem root_inverse_eq_responseFrame_norm_of_ae
    (M : ABKModel 2) (Q : TriadicCube 2) (m N K₀ : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (k : ResponseCoefficient (openCubeSet Q))
    (hcoef : responsePlanarCoefficientField M.nu k =ᵐ[volume.restrict (cubeSet Q)]
      attenuatedCoefficient M m N weights ω) :
    rootInverseObservable M Q m N K₀ weights ω =
      Book.Ch02.matrixNorm
        (coarseBlockMatrix (cubeSet Q)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M K₀ : ℝ) k)).lowerRight := by
  have hσ₀ : 0 < (Annealed.sigmaBar M K₀ : ℝ) :=
    (Annealed.sigmaBar_characterization M K₀).1
  have hσm : 0 < (Annealed.sigmaBar M m : ℝ) :=
    (Annealed.sigmaBar_characterization M m).1
  have hcoarse :
      coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu k) =
        coarseBlockMatrix (cubeSet Q)
          (attenuatedCoefficient M m N weights ω) :=
    coarseBlockMatrix_congr_of_ae_eq hcoef
  have hframe := cir_response_coarseMatrix_frame_eq Q M.nu
    (Annealed.sigmaBar M K₀ : ℝ) M.nu_pos hσ₀ k
  rw [root_inverse_observable_eq_reference_ratio]
  have hg3 : rootInverseResponse M Q m N weights ω =
      (Annealed.sigmaBar M m : ℝ) *
        Book.Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet Q)
            (attenuatedCoefficient M m N weights ω)).lowerRight := by
    simp only [rootInverseResponse, Book.Ch02.matrixNorm]
  rw [hg3, ← hcoarse, hframe]
  simp only [frameMatrix]
  rw [ASDExplicitGamma.Scalar.inverse_history_matrixNorm_smul _ _ hσ₀.le]
  field_simp [hσm.ne']

/-- On an actual one-shell insertion path, the reset trace profile is the
translated-square trace of the same partially inserted coefficient. -/
theorem aoCir_step_trace_eq_squareTrace
    (M : ABKModel 2) (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (m N K₀ : ℤ) (hmN : m < N) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    rootTraceObservable M Q m N K₀ (aoCirStepWeights N t) ω =
      squareTrace Q M.nu (Annealed.sigmaBar M K₀ : ℝ)
        (cirSquareRestrictionCLM Q hQ
          (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
            (N - 1) t ω)) + 4 := by
  let K := closure (cubeSet (originCube 2 n))
  let k : ResponseCoefficient (openCubeSet Q) :=
    cirSquareRestrictionCLM Q hQ (modelInsertedScalar K (N - 1) t ω)
  have hAttenuated : attenuatedCoefficient M m N (aoCirStepWeights N t) ω =
      Model.partialInsertedCoefficient M (N - 1) t ω := by
    funext x
    exact aoCir_step_coefficient M m N hmN t ω x
  have hphysical : ∀ x ∈ openCubeSet Q,
      responsePlanarCoefficientField M.nu k x =
        Model.partialInsertedCoefficient M (N - 1) t ω x := by
    intro x hx
    have hxK : x ∈ K := hQ (subset_closure hx)
    have hkx : k ⟨x, subset_closure hx⟩ =
        modelInsertedScalar K (N - 1) t ω ⟨x, hxK⟩ := by
      change modelInsertedScalar K (N - 1) t ω
          ⟨x, hQ (subset_closure hx)⟩ = _
      rfl
    have hscalar := modelInsertedScalar_apply K M ell (N - 1) hK t ω ⟨x, hxK⟩
    rw [responsePlanarCoefficientField, responseCoefficientExtension_eq k hx,
      hkx, hscalar]
    exact cir_planarCoefficient_eq_of_symmPart M.nu _
      (cir_symmPart_modelInserted M (N - 1) t ω x)
  have hphysicalAE : responsePlanarCoefficientField M.nu k =ᵐ[
      volume.restrict (cubeSet Q)]
      Model.partialInsertedCoefficient M (N - 1) t ω := by
    have hopen : responsePlanarCoefficientField M.nu k =ᵐ[
        volume.restrict (openCubeSet Q)]
        Model.partialInsertedCoefficient M (N - 1) t ω := by
      filter_upwards [ae_restrict_mem (μ := volume)
        (measurableSet_openCubeSet Q)] with x hx
      exact hphysical x hx
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact hopen
  have hcoef : responsePlanarCoefficientField M.nu k =ᵐ[
      volume.restrict (cubeSet Q)]
      attenuatedCoefficient M m N (aoCirStepWeights N t) ω := by
    filter_upwards [hphysicalAE] with x hx
    rw [hAttenuated]
    exact hx
  exact root_trace_eq_squareTrace_of_ae M Q m N K₀
    (aoCirStepWeights N t) ω k hcoef

/-- On an actual one-shell insertion path, the reset inverse root is the
operator norm of the response-frame inverse block on the same square. -/
theorem aoCir_step_inverse_eq_responseFrame_norm
    (M : ABKModel 2) (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (m N K₀ : ℤ) (hmN : m < N) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    rootInverseObservable M Q m N K₀ (aoCirStepWeights N t) ω =
      Book.Ch02.matrixNorm
        (coarseBlockMatrix (cubeSet Q)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M K₀ : ℝ)
            (cirSquareRestrictionCLM Q hQ
              (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
                (N - 1) t ω)))).lowerRight := by
  let K := closure (cubeSet (originCube 2 n))
  let k : ResponseCoefficient (openCubeSet Q) :=
    cirSquareRestrictionCLM Q hQ (modelInsertedScalar K (N - 1) t ω)
  have hAttenuated : attenuatedCoefficient M m N (aoCirStepWeights N t) ω =
      Model.partialInsertedCoefficient M (N - 1) t ω := by
    funext x
    exact aoCir_step_coefficient M m N hmN t ω x
  have hphysical : ∀ x ∈ openCubeSet Q,
      responsePlanarCoefficientField M.nu k x =
        Model.partialInsertedCoefficient M (N - 1) t ω x := by
    intro x hx
    have hxK : x ∈ K := hQ (subset_closure hx)
    have hkx : k ⟨x, subset_closure hx⟩ =
        modelInsertedScalar K (N - 1) t ω ⟨x, hxK⟩ := by
      change modelInsertedScalar K (N - 1) t ω
          ⟨x, hQ (subset_closure hx)⟩ = _
      rfl
    have hscalar := modelInsertedScalar_apply K M ell (N - 1) hK t ω ⟨x, hxK⟩
    rw [responsePlanarCoefficientField, responseCoefficientExtension_eq k hx,
      hkx, hscalar]
    exact cir_planarCoefficient_eq_of_symmPart M.nu _
      (cir_symmPart_modelInserted M (N - 1) t ω x)
  have hphysicalAE : responsePlanarCoefficientField M.nu k =ᵐ[
      volume.restrict (cubeSet Q)]
      Model.partialInsertedCoefficient M (N - 1) t ω := by
    have hopen : responsePlanarCoefficientField M.nu k =ᵐ[
        volume.restrict (openCubeSet Q)]
        Model.partialInsertedCoefficient M (N - 1) t ω := by
      filter_upwards [ae_restrict_mem (μ := volume)
        (measurableSet_openCubeSet Q)] with x hx
      exact hphysical x hx
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact hopen
  have hcoef : responsePlanarCoefficientField M.nu k =ᵐ[
      volume.restrict (cubeSet Q)]
      attenuatedCoefficient M m N (aoCirStepWeights N t) ω := by
    filter_upwards [hphysicalAE] with x hx
    rw [hAttenuated]
    exact hx
  exact root_inverse_eq_responseFrame_norm_of_ae M Q m N K₀
    (aoCirStepWeights N t) ω k hcoef

end ASDExplicitGamma.AllOrder
