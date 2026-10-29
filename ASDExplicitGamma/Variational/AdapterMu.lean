module

public import ASDExplicitGamma.Variational.AdapterAmplitude
public import ASDExplicitGamma.Response.Analytic

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization ASDExplicitGamma.Response

noncomputable section

-- The deterministic/canonical realization comparison follows the established
-- Response.Analytic proof, here exposing the translated-square conclusion.
private theorem response_muHilbertRealization_ext
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

private theorem response_muCandidate_eq_of_hilbert_fields
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuHilbertRealization U a)
    (hc : M.correctionSpace = N.correctionSpace)
    (hl : M.constantField = N.constantField)
    (he : M.energyBilin = N.energyBilin) (P : BlockVec 2) :
    M.muCandidate P = N.muCandidate P := by
  exact congrArg (fun R : MuHilbertRealization U a => R.muCandidate P)
    (response_muHilbertRealization_ext M N hc hl he)

private theorem response_muOperatorRealization_operator_eq
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuOperatorRealization U a)
    (h : ∀ F : HilbertBlockL2 U, M.operator F =ᵐ[volumeMeasureOn U] N.operator F) :
    M.operator = N.operator := by
  ext F
  exact h F

private theorem response_deterministic_operator_eq_canonicalAEE
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
  apply response_muOperatorRealization_operator_eq
    M.toMuOperatorRealization N.toMuOperatorRealization
  intro F
  filter_upwards [
    M.toMuOperatorRealization.ae_apply F,
    N.toMuOperatorRealization.ae_apply F]
    with x hdet haee
  rw [hdet, haee]

private theorem response_deterministic_correctionSpace_eq_canonicalAEE
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

private theorem response_deterministic_constantField_eq_canonicalAEE
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

private theorem response_energyBilin_eq_of_operator_eq
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuOperatorRealization U a) (h : M.operator = N.operator) :
    energyBilinOfOperator M.operator = energyBilinOfOperator N.operator := by
  rw [h]

theorem response_deterministic_muCandidate_eq_mu_triCube
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
    exact response_deterministic_operator_eq_canonicalAEE aSlice hEll
  have hEnergy : Hdet.energyBilin = Haee.energyBilin := by
    change energyBilinOfOperator Mdet.toMuOperatorRealization.operator =
      energyBilinOfOperator Maee.toMuOperatorRealization.operator
    exact response_energyBilin_eq_of_operator_eq
      Mdet.toMuOperatorRealization Maee.toMuOperatorRealization hOp
  calc
    Hdet.muCandidate P = Haee.muCandidate P :=
      response_muCandidate_eq_of_hilbert_fields Hdet Haee
        (response_deterministic_correctionSpace_eq_canonicalAEE aSlice hEll)
        (response_deterministic_constantField_eq_canonicalAEE aSlice hEll)
        hEnergy P
    _ = Mu (cubeSet Q) P a :=
      (mu_eq_canonicalAEEMuCandidate Q j aSlice P).symm

private theorem responseFrameEnergyObservable_eq_twice_frameMuCandidate
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

private theorem response_planarFrameCoefficient_eq_smul_unit
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

private theorem response_planarCoefficientField_eq_smul_unit_on
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

theorem response_coarseMatrix_frame_eq {Q : TriadicCube 2}
    (hU : MeasurableSet (cubeSet Q))
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (cubeSet Q)) :
    coarseBlockMatrix (cubeSet Q)
        (responseFramePlanarCoefficientField ν σ k) =
      frameMatrix σ (coarseBlockMatrix (cubeSet Q)
        (responsePlanarCoefficientField ν k)) := by
  let U := cubeSet Q
  let a₁ := responsePlanarCoefficientField 1 (ν⁻¹ • k)
  have hEll₁ : IsEllipticFieldOn 1 (1 + ‖ν⁻¹ • k‖ ^ 2) U a₁ := by
    simpa using responsePlanarCoefficientField_isElliptic hU 1 (by norm_num) (ν⁻¹ • k)
  have hCoeffFrameOn (x : Vec 2) (hx : x ∈ U) :
      responseFramePlanarCoefficientField ν σ k x = ((ν / σ) • a₁) x :=
    response_planarFrameCoefficient_eq_smul_unit ν σ hν hσ k x hx
  have hCoeffPhysicalOn (x : Vec 2) (hx : x ∈ U) :
      responsePlanarCoefficientField ν k x = (ν • a₁) x :=
    response_planarCoefficientField_eq_smul_unit_on ν hν k x hx
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

theorem responseFrameEnergyObservable_eq_frameCoarseQuadratic
    {Q : TriadicCube 2} (hU : MeasurableSet (cubeSet Q))
    (hvol : 0 < (MeasureTheory.volume (cubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k : ResponseCoefficient (cubeSet Q)) :
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
      blockVecDot P (blockMatVecMul
        (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField ν k))) P) := by
  have hEll := responseFramePlanarCoefficientField_isElliptic hU ν σ hν hσ k
  have hMu := response_deterministic_muCandidate_eq_mu_triCube
    (Q := Q) (div_pos hν hσ) hEll P
  have hCandidate :
      (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.muCandidate P =
        Mu (cubeSet Q) P (responseFramePlanarCoefficientField ν σ k) := by
    simpa [responseFrameMuOperatorSystemData] using hMu
  calc
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
        2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.muCandidate P :=
          responseFrameEnergyObservable_eq_twice_frameMuCandidate hU hvol ν σ hν hσ P k
    _ =
        2 * Mu (cubeSet Q) P
          (responseFramePlanarCoefficientField ν σ k) := by rw [hCandidate]
    _ = blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (cubeSet Q)
            (responseFramePlanarCoefficientField ν σ k)) P) := by
          rw [mu_eq_half_coarseBlockMatrix_elliptic_triCube
            (div_pos hν hσ) hEll P]
          ring
    _ = blockVecDot P (blockMatVecMul
          (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
            (responsePlanarCoefficientField ν k))) P) := by
          rw [response_coarseMatrix_frame_eq hU ν σ hν hσ k]


private theorem adapter_isEllipticMatrix_inv_smul {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix 1 (Lam / lam) (lam⁻¹ • A) := by
  rcases hA with ⟨hlam, hle, hlower, hinv⟩
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hle
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix ⟨hlam, hle, hlower, hinv⟩
  have hinvScale := nonsing_inv_smul lam⁻¹ (inv_ne_zero hlam.ne') hdet
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · have hdiv : lam / lam ≤ Lam / lam := div_le_div_of_nonneg_right hle hlam.le
    simpa [div_self hlam.ne'] using hdiv
  · intro ξ
    rw [smul_matVecMul, vecDot_smul_right]
    calc
      1 * vecNormSq ξ = lam⁻¹ * (lam * vecNormSq ξ) := by field_simp [hlam.ne']
      _ ≤ lam⁻¹ * vecDot ξ (matVecMul A ξ) :=
        mul_le_mul_of_nonneg_left (hlower ξ) (inv_nonneg.mpr hlam.le)
  · intro ξ
    have hscale : (Lam / lam)⁻¹ = lam * Lam⁻¹ := by
      field_simp [hlam.ne', hLam.ne']
    calc
      (Lam / lam)⁻¹ * vecNormSq ξ = lam * (Lam⁻¹ * vecNormSq ξ) := by
        rw [hscale]
        ring
      _ ≤ lam * vecDot ξ (matVecMul A⁻¹ ξ) :=
        mul_le_mul_of_nonneg_left (hinv ξ) hlam.le
      _ = vecDot ξ (matVecMul (lam⁻¹ • A)⁻¹ ξ) := by
        rw [hinvScale]
        simp [smul_matVecMul, vecDot_smul_right, inv_inv]

theorem normalized_isEllipticFieldOn {d : ℕ} {U : Set (Vec d)}
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn 1 (Lam / lam) U (lam⁻¹ • a) := by
  classical
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    have hrow : Measurable (fun x => if x ∈ U then a x i j else 0) :=
      (measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 i)) j
    simpa [Pi.smul_apply, smul_eq_mul] using hrow.const_mul lam⁻¹
  · intro x hx
    exact adapter_isEllipticMatrix_inv_smul (hEll.2 x hx)


/-- Exact frame normalization; the molecular coefficient and frame remain distinct. -/
theorem frameMatrix_coarseBlockMatrix_normalize {Q : TriadicCube 2}
    {ν Λ σ : ℝ} {a : CoeffField 2} (hν : 0 < ν)
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) (hσ : 0 < σ) :
    frameMatrix σ (coarseBlockMatrix (cubeSet Q) a) =
      frameMatrix (σ / ν) (coarseBlockMatrix (cubeSet Q) (ν⁻¹ • a)) := by
  rw [coarseBlockMatrix_smul_elliptic_triCube hν hEll (inv_pos.mpr hν)]
  have hs : (Real.sqrt ν⁻¹) ^ 2 = ν⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hν.le)
  have hi : (Real.sqrt ν⁻¹) ^ (-2 : ℤ) = ν := by
    rw [zpow_neg, zpow_ofNat, hs, inv_inv]
  cases coarseBlockMatrix (cubeSet Q) a with
  | mk ul ur ll lr =>
    simp only [frameMatrix, coarseMatrixRescale, BlockMat.mk.injEq]
    refine ⟨?_, trivial, trivial, ?_⟩ <;> ext i j <;>
      simp only [Matrix.smul_apply, smul_eq_mul, hs, hi] <;>
      field_simp [hν.ne', hσ.ne']

/-- Source coefficient-amplitude congruence, discharging ellipticity from k. -/
theorem response_coarseBlockMatrix_smul (Q : TriadicCube 2) (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient (cubeSet Q)) (c : ℝ) (hc : 0 < c) :
    coarseBlockMatrix (cubeSet Q) (c • responsePlanarCoefficientField ν k) =
      coarseMatrixRescale (Real.sqrt c)
        (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)) :=
  coarseBlockMatrix_smul_elliptic_triCube hν
    (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k) hc

/-- Source minimum scaling with no separately supplied ellipticity proof. -/
theorem response_Mu_smul (Q : TriadicCube 2) (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient (cubeSet Q)) (c : ℝ) (hc : 0 < c) (P : BlockVec 2) :
    Mu (cubeSet Q) P (c • responsePlanarCoefficientField ν k) =
      Mu (cubeSet Q) (loadRescale (Real.sqrt c) P) (responsePlanarCoefficientField ν k) :=
  Mu_smul_eq (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k)
    (measurableSet_cubeSet Q) hc P

/-- The source frame normalization, retaining σ distinct from ν. -/
theorem response_frameMatrix_normalize (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (cubeSet Q)) :
    frameMatrix σ (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)) =
      frameMatrix (σ / ν) (coarseBlockMatrix (cubeSet Q) (ν⁻¹ • responsePlanarCoefficientField ν k)) :=
  frameMatrix_coarseBlockMatrix_normalize hν
    (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k) hσ

/-- The actual normalized coefficient is unit elliptic on the source cell. -/
theorem response_normalized_isElliptic (Q : TriadicCube 2) (ν : ℝ)
    (hν : 0 < ν) (k : ResponseCoefficient (cubeSet Q)) :
    IsEllipticFieldOn 1 (((ν ^ 2 + ‖k‖ ^ 2) / ν) / ν) (cubeSet Q)
      (ν⁻¹ • responsePlanarCoefficientField ν k) :=
  normalized_isEllipticFieldOn
    (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k)

/-- Exact normalized coarse characterization on every translated square. -/
theorem response_normalized_Mu_eq_quadratic (Q : TriadicCube 2) (ν : ℝ)
    (hν : 0 < ν) (k : ResponseCoefficient (cubeSet Q)) (P : BlockVec 2) :
    2 * Mu (cubeSet Q) P (ν⁻¹ • responsePlanarCoefficientField ν k) =
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (cubeSet Q) (ν⁻¹ • responsePlanarCoefficientField ν k)) P) := by
  rw [mu_eq_half_coarseBlockMatrix_elliptic_triCube (by norm_num : (0 : ℝ) < 1)
    (response_normalized_isElliptic Q ν hν k)]
  ring

end

end ASDExplicitGamma.Variational
