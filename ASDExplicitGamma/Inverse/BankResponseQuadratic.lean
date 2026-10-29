module

public import ASDExplicitGamma.Response.Analytic

/-! The arbitrary-load response and literal coarse quadratic agree.
The canonical-Hilbert-space comparison follows Response.Analytic's trace bridge. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational

noncomputable section

private theorem bank_response_muHilbertRealization_ext
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuHilbertRealization U a)
    (hc : M.correctionSpace = N.correctionSpace)
    (hl : M.constantField = N.constantField)
    (he : M.energyBilin = N.energyBilin) : M = N := by
  cases M with
  | mk cm lm em sm cm' =>
    cases N with
    | mk cn ln en sn cn' =>
      simp only [MuHilbertRealization.mk.injEq]
      exact ⟨by simpa using hc, by simpa using hl, by simpa using he⟩

private theorem bank_response_muCandidate_eq_of_hilbert_fields
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuHilbertRealization U a)
    (hc : M.correctionSpace = N.correctionSpace)
    (hl : M.constantField = N.constantField)
    (he : M.energyBilin = N.energyBilin) (P : BlockVec 2) :
    M.muCandidate P = N.muCandidate P := by
  exact congrArg (fun R : MuHilbertRealization U a => R.muCandidate P)
    (bank_response_muHilbertRealization_ext M N hc hl he)

private theorem bank_response_muOperatorRealization_operator_eq
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuOperatorRealization U a)
    (h : ∀ F : HilbertBlockL2 U, M.operator F =ᵐ[volumeMeasureOn U] N.operator F) :
    M.operator = N.operator := by
  ext F
  exact h F

private theorem bank_response_deterministic_operator_eq_canonicalAEE
    {Q : TriadicCube 2} {j : ℕ}
    (aSlice : {a : CoeffField 2 // AEEQuantitativeEllipticSlice (cubeSet Q) j a})
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) aSlice.1) :
    (PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)).toMuOperatorRealization.operator =
    (canonicalAEEMuOperatorSystemData Q j aSlice).toMuOperatorRealization.operator := by
  let M : MuOperatorSystemData (cubeSet Q) aSlice.1 :=
    PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)
  let N : AEEMuOperatorSystemData (cubeSet Q) aSlice.1 :=
    canonicalAEEMuOperatorSystemData Q j aSlice
  change M.toMuOperatorRealization.operator = N.toMuOperatorRealization.operator
  apply bank_response_muOperatorRealization_operator_eq
    M.toMuOperatorRealization N.toMuOperatorRealization
  intro F
  filter_upwards [
    M.toMuOperatorRealization.ae_apply F,
    N.toMuOperatorRealization.ae_apply F]
    with x hdet haee
  rw [hdet, haee]

private theorem bank_response_deterministic_correctionSpace_eq_canonicalAEE
    {Q : TriadicCube 2} {j : ℕ}
    (aSlice : {a : CoeffField 2 // AEEQuantitativeEllipticSlice (cubeSet Q) j a})
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) aSlice.1) :
    (PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)).toMuHilbertRealization.correctionSpace =
    (canonicalAEEMuOperatorSystemData Q j aSlice).toMuHilbertRealization.correctionSpace := by
  simp only [PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn,
    PotentialSolenoidalL2Data.correctionSpace_toMuOperatorSystemData,
    MuOperatorSystemData.toMuHilbertRealization,
    MuOperatorSystemData.toMuOperatorRealization,
    MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
    AEEMuOperatorSystemData.toMuHilbertRealization,
    AEEMuOperatorSystemData.toMuOperatorRealization,
    correctionSpace_canonicalAEEMuOperatorSystemData,
    canonicalAEEMuCorrectionSpaceData, canonicalAEEPotentialSolenoidalL2Data]

private theorem bank_response_deterministic_constantField_eq_canonicalAEE
    {Q : TriadicCube 2} {j : ℕ}
    (aSlice : {a : CoeffField 2 // AEEQuantitativeEllipticSlice (cubeSet Q) j a})
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) aSlice.1) :
    (PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)).toMuHilbertRealization.constantField =
    (canonicalAEEMuOperatorSystemData Q j aSlice).toMuHilbertRealization.constantField := by
  simp only [PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn,
    PotentialSolenoidalL2Data.toMuOperatorSystemData,
    MuOperatorSystemData.toMuHilbertRealization,
    MuOperatorSystemData.toMuOperatorRealization,
    MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
    canonicalAEEMuOperatorSystemData, canonicalAEEMuCorrectionSpaceData,
    canonicalAEEPotentialSolenoidalL2Data, canonicalAEEMuCoeffOperatorData,
    AEEMuCoeffOperatorData.toMuOperatorRealization,
    AEEMuOperatorSystemData.toMuOperatorRealization,
    AEEMuOperatorSystemData.toMuHilbertRealization]

private theorem bank_response_energyBilin_eq_of_operator_eq
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuOperatorRealization U a) (h : M.operator = N.operator) :
    energyBilinOfOperator M.operator = energyBilinOfOperator N.operator := by
  rw [h]

private theorem bank_response_deterministic_muCandidate_eq_mu_triCube
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (P : BlockVec 2) :
    (PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)).toMuHilbertRealization.muCandidate P =
      Mu (cubeSet Q) P a := by
  have hAEE := IsAEEllipticFieldOn.of_isEllipticFieldOn hEll
  obtain ⟨j, hj⟩ := AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn hlam hAEE
  let aSlice : {a : CoeffField 2 // AEEQuantitativeEllipticSlice (cubeSet Q) j a} :=
    ⟨a, hj⟩
  let Mdet : MuOperatorSystemData (cubeSet Q) a :=
    PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)
  let Maee : AEEMuOperatorSystemData (cubeSet Q) a :=
    canonicalAEEMuOperatorSystemData Q j aSlice
  let Hdet := Mdet.toMuHilbertRealization
  let Haee := Maee.toMuHilbertRealization
  have hOp : Mdet.toMuOperatorRealization.operator =
      Maee.toMuOperatorRealization.operator := by
    exact bank_response_deterministic_operator_eq_canonicalAEE aSlice hEll
  have hEnergy : Hdet.energyBilin = Haee.energyBilin := by
    change energyBilinOfOperator Mdet.toMuOperatorRealization.operator =
      energyBilinOfOperator Maee.toMuOperatorRealization.operator
    exact bank_response_energyBilin_eq_of_operator_eq
      Mdet.toMuOperatorRealization Maee.toMuOperatorRealization hOp
  calc
    Hdet.muCandidate P = Haee.muCandidate P :=
      bank_response_muCandidate_eq_of_hilbert_fields Hdet Haee
        (bank_response_deterministic_correctionSpace_eq_canonicalAEE aSlice hEll)
        (bank_response_deterministic_constantField_eq_canonicalAEE aSlice hEll)
        hEnergy P
    _ = Mu (cubeSet Q) P a :=
      (mu_eq_canonicalAEEMuCandidate Q j aSlice P).symm

private theorem bank_responseFrameEnergyObservable_eq_twice_frameMuCandidate
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k : ResponseCoefficient U) :
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
      2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.muCandidate P := by
  simp only [responseFrameEnergyObservable, responseFrameEnergy]
  exact congrArg
    (fun z : ResponseCoefficient U =>
      2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ z).toMuHilbertRealization.muCandidate P)
    (zero_add k)

private theorem bank_response_planarFrameCoefficient_eq_smul_unit
    {U : Set (Vec 2)} (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (x : Vec 2) (hx : x ∈ U) :
    responseFramePlanarCoefficientField ν σ k x =
      ((ν / σ) • responsePlanarCoefficientField 1 (ν⁻¹ • k)) x := by
  unfold responseFramePlanarCoefficientField responsePlanarCoefficientField
  change responsePlanarCoefficient (ν / σ) (responseCoefficientExtension k x / σ) =
    (ν / σ) • responsePlanarCoefficient 1 (responseCoefficientExtension (ν⁻¹ • k) x)
  rw [responseCoefficientExtension_smul_on (ν⁻¹) k hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ, Matrix.smul_apply, smul_eq_mul]
  <;> field_simp [hν.ne', hσ.ne']

private theorem bank_response_planarCoefficientField_eq_smul_unit_on
    {U : Set (Vec 2)} (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient U) (x : Vec 2) (hx : x ∈ U) :
    responsePlanarCoefficientField ν k x =
      (ν • responsePlanarCoefficientField 1 (ν⁻¹ • k)) x := by
  unfold responsePlanarCoefficientField
  change responsePlanarCoefficient ν (responseCoefficientExtension k x) =
    ν • responsePlanarCoefficient 1 (responseCoefficientExtension (ν⁻¹ • k) x)
  rw [responseCoefficientExtension_smul_on (ν⁻¹) k hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ, Matrix.smul_apply, smul_eq_mul]
  <;> field_simp [hν.ne']

private theorem bank_response_coarseMatrix_frame_eq {m : ℤ}
    (hU : MeasurableSet (cubeSet (originCube 2 m)))
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (cubeSet (originCube 2 m))) :
    coarseBlockMatrix (cubeSet (originCube 2 m))
        (responseFramePlanarCoefficientField ν σ k) =
      frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 m))
        (responsePlanarCoefficientField ν k)) := by
  let U := cubeSet (originCube 2 m)
  let a₁ := responsePlanarCoefficientField 1 (ν⁻¹ • k)
  have hEll₁ : IsEllipticFieldOn 1 (1 + ‖ν⁻¹ • k‖ ^ 2) U a₁ := by
    simpa using responsePlanarCoefficientField_isElliptic hU 1 (by norm_num) (ν⁻¹ • k)
  have hCoeffFrameOn (x : Vec 2) (hx : x ∈ U) :
      responseFramePlanarCoefficientField ν σ k x = ((ν / σ) • a₁) x :=
    bank_response_planarFrameCoefficient_eq_smul_unit ν σ hν hσ k x hx
  have hCoeffPhysicalOn (x : Vec 2) (hx : x ∈ U) :
      responsePlanarCoefficientField ν k x = (ν • a₁) x :=
    bank_response_planarCoefficientField_eq_smul_unit_on ν hν k x hx
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsν_sq : (Real.sqrt ν) ^ 2 = ν := Real.sq_sqrt hν.le
  have hCoeffPhysical' : ∀ x ∈ U,
      responsePlanarCoefficientField ν k x = ((Real.sqrt ν) ^ 2 • a₁) x := by
    intro x hx
    rw [hsν_sq]
    exact hCoeffPhysicalOn x hx
  have hCoarsePhysical :
      coarseBlockMatrix U (responsePlanarCoefficientField ν k) =
        coarseMatrixRescale (Real.sqrt ν) (coarseBlockMatrix U a₁) := by
    have hAE : responsePlanarCoefficientField ν k =ᵐ[MeasureTheory.volume.restrict U]
        ((Real.sqrt ν) ^ 2 • a₁) := by
      filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
      exact hCoeffPhysical' x hx
    rw [coarseBlockMatrix_congr_of_ae_eq hAE]
    exact coarseBlockMatrix_sq_smul_triCube hEll₁ hsν
  have hsFrame : 0 < Real.sqrt (ν / σ) :=
    Real.sqrt_pos.2 (div_pos hν hσ)
  have hsFrame_sq : (Real.sqrt (ν / σ)) ^ 2 = ν / σ :=
    Real.sq_sqrt (div_nonneg hν.le hσ.le)
  have hCoeffFrame' : ∀ x ∈ U,
      responseFramePlanarCoefficientField ν σ k x =
        ((Real.sqrt (ν / σ)) ^ 2 • a₁) x := by
    intro x hx
    rw [hsFrame_sq]
    exact hCoeffFrameOn x hx
  have hCoarseFrame :
      coarseBlockMatrix U (responseFramePlanarCoefficientField ν σ k) =
        coarseMatrixRescale (Real.sqrt (ν / σ)) (coarseBlockMatrix U a₁) := by
    have hAE : responseFramePlanarCoefficientField ν σ k =ᵐ[MeasureTheory.volume.restrict U]
        ((Real.sqrt (ν / σ)) ^ 2 • a₁) := by
      filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
      exact hCoeffFrame' x hx
    rw [coarseBlockMatrix_congr_of_ae_eq hAE]
    exact coarseBlockMatrix_sq_smul_triCube hEll₁ hsFrame
  have hRescale :
      coarseMatrixRescale (Real.sqrt (ν / σ)) (coarseBlockMatrix U a₁) =
        frameMatrix σ (coarseMatrixRescale (Real.sqrt ν) (coarseBlockMatrix U a₁)) := by
    have hInvFrame : (Real.sqrt (ν / σ)) ^ (-2 : ℤ) = σ / ν := by
      rw [zpow_neg, zpow_ofNat, hsFrame_sq]
      field_simp [hν.ne', hσ.ne']
    have hInvν : (Real.sqrt ν) ^ (-2 : ℤ) = ν⁻¹ := by
      rw [zpow_neg, zpow_ofNat, hsν_sq]
    cases coarseBlockMatrix U a₁ with
    | mk ul ur ll lr =>
      have hUL : (Real.sqrt (ν / σ)) ^ 2 • ul =
          σ⁻¹ • ((Real.sqrt ν) ^ 2 • ul) := by
        ext i j
        simp [Matrix.smul_apply, smul_eq_mul, hsFrame_sq, hsν_sq]
        ; field_simp [hν.ne', hσ.ne']
      have hLR : (Real.sqrt (ν / σ)) ^ (-2 : ℤ) • lr =
          σ • ((Real.sqrt ν) ^ (-2 : ℤ) • lr) := by
        ext i j
        simp [Matrix.smul_apply, smul_eq_mul, hInvFrame, hInvν]
        ; field_simp [hν.ne', hσ.ne']
      simp only [coarseMatrixRescale, frameMatrix, BlockMat.mk.injEq]
      exact ⟨hUL, trivial, trivial, hLR⟩
  rw [hCoarseFrame, hCoarsePhysical, hRescale]

theorem bank_responseFrameEnergyObservable_eq_frameCoarseQuadratic
    {m : ℤ} (hU : MeasurableSet (cubeSet (originCube 2 m)))
    (hvol : 0 < (MeasureTheory.volume (cubeSet (originCube 2 m))).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k : ResponseCoefficient (cubeSet (originCube 2 m))) :
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
      blockVecDot P (blockMatVecMul
        (frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 m))
          (responsePlanarCoefficientField ν k))) P) := by
  have hEll := responseFramePlanarCoefficientField_isElliptic hU ν σ hν hσ k
  have hMu := bank_response_deterministic_muCandidate_eq_mu_triCube
    (Q := originCube 2 m) (div_pos hν hσ) hEll P
  have hCandidate :
      (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.muCandidate P =
        Mu (cubeSet (originCube 2 m)) P (responseFramePlanarCoefficientField ν σ k) := by
    simpa [responseFrameMuOperatorSystemData] using hMu
  calc
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
        2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.muCandidate P :=
          bank_responseFrameEnergyObservable_eq_twice_frameMuCandidate hU hvol ν σ hν hσ P k
    _ =
        2 * Mu (cubeSet (originCube 2 m)) P
          (responseFramePlanarCoefficientField ν σ k) := by rw [hCandidate]
    _ = blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (cubeSet (originCube 2 m))
            (responseFramePlanarCoefficientField ν σ k)) P) := by
          rw [mu_eq_half_coarseBlockMatrix_elliptic_triCube
            (div_pos hν hσ) hEll P]
          ring
    _ = blockVecDot P (blockMatVecMul
          (frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 m))
            (responsePlanarCoefficientField ν k))) P) := by
          rw [bank_response_coarseMatrix_frame_eq hU ν σ hν hσ k]


end
end ASDExplicitGamma.Inverse
