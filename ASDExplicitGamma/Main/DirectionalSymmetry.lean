module

public import ASDExplicitGamma.Main.DirectionalCovarianceTrace
public import ASDExplicitGamma.Main.DirectionalPhysicalFlux
public import ASDExplicitGamma.Model.CellSymmetry
public import ASDExplicitGamma.Scalar.SmoothFeedback
public import ASDExplicitGamma.Scalar.SmoothFeedbackCellRotation
public import ASDExplicitGamma.Scalar.SpatialQuarterTurnHaar

/-! Source-level quarter-turn covariance for the actual directional Gram
matrices of the OLD-frame partial insertion. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Native
open ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff

private theorem main_scalarCellResponseTest_admissible
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    IsBlockMuAdmissible (openCubeSet Q) P (scalarCellResponseTest Q a hEll P) := by
  have h := scalar_cell_response_test_variation Q a hEll P
  refine ⟨memVectorL2_fst_of_memBlockL2 h.1, ?_,
    memVectorL2_snd_of_memBlockL2 h.1, ?_⟩
  · simpa [BlockState.eval] using h.2.1
  · simpa [BlockState.eval] using h.2.2

private theorem main_scalarCellResponseTest_energy_eq_Mu
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    blockEnergyAverage (openCubeSet Q) a (scalarCellResponseTest Q a hEll P) =
      Mu (openCubeSet Q) P a := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let _ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hU.isFiniteMeasure_restrict_volume
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  let M := scalarCellSystem Q a hEll
  have hmu : ∀ T : BlockVec 2,
      Mu (openCubeSet Q) T a = M.toMuHilbertRealization.muCandidate T := by
    intro T
    exact (lemmaV_canonical_muCandidate_eq_Mu hU hEll
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) T).symm
  have h := R.recoveredField_blockEnergyAverage_eq_mu M hmu P
  simpa [R, M, scalarCellSystem, scalarCellResponseTest] using h

private theorem main_blockEnergyAverage_congr_coeff_ae
    (Q : TriadicCube 2) (a a' : CoeffField 2)
    (hae : a =ᵐ[volumeMeasureOn (openCubeSet Q)] a') (X : BlockState 2) :
    blockEnergyAverage (openCubeSet Q) a X =
      blockEnergyAverage (openCubeSet Q) a' X := by
  unfold blockEnergyAverage volumeAverage
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp [blockEnergyDensity, blockCoeffField, hx]

/-- The canonical affine cell minimizer is unchanged, as an L2 field, by an
almost-everywhere change to its coefficient. This is the bridge from the
actual rotated cutoff coefficient to the exact cell-symmetry coefficient. -/
theorem main_scalarCellResponseTest_congr_coeff_ae
    (Q : TriadicCube 2) (a a' : CoeffField 2) {lam Lam lam' Lam' : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hEll' : IsEllipticFieldOn lam' Lam' (openCubeSet Q) a')
    (hae : a =ᵐ[volumeMeasureOn (openCubeSet Q)] a') (P : BlockVec 2) :
    (scalarCellResponseTest Q a hEll P).eval =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q a' hEll' P).eval := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let _ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hU.isFiniteMeasure_restrict_volume
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  let M := scalarCellSystem Q a hEll
  let X := scalarCellResponseTest Q a hEll P
  let Y := scalarCellResponseTest Q a' hEll' P
  have hXadm : IsBlockMuAdmissible (openCubeSet Q) P X :=
    main_scalarCellResponseTest_admissible Q a hEll P
  have hYadm : IsBlockMuAdmissible (openCubeSet Q) P Y :=
    main_scalarCellResponseTest_admissible Q a' hEll' P
  have hmu : ∀ T : BlockVec 2,
      Mu (openCubeSet Q) T a = M.toMuHilbertRealization.muCandidate T := by
    intro T
    exact (lemmaV_canonical_muCandidate_eq_Mu hU hEll
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) T).symm
  have henergyY : blockEnergyAverage (openCubeSet Q) a Y =
      Mu (openCubeSet Q) P a := by
    calc
      blockEnergyAverage (openCubeSet Q) a Y =
          blockEnergyAverage (openCubeSet Q) a' Y :=
        main_blockEnergyAverage_congr_coeff_ae Q a a' hae Y
      _ = Mu (openCubeSet Q) P a' := by
        simpa [Y] using main_scalarCellResponseTest_energy_eq_Mu Q a' hEll' P
      _ = Mu (openCubeSet Q) P a :=
        (Mu_congr_of_ae_eq hae P).symm
  have hminY : toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval =
      M.toMuHilbertRealization.minimizerMap P := by
    apply M.toMuHilbertRealization.eq_minimizerMap_of_quadraticEnergy_le_muCandidate
      P (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval) ?_ ?_
    · exact hYadm.toCorrectionFieldData_mem_correctionSpace
    · change quadraticEnergy (energyBilinOfOperator M.toMuOperatorRealization.operator)
        (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval) ≤
          M.toMuHilbertRealization.muCandidate P
      rw [M.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        (X := Y) hYadm.memBlockL2_eval]
      rw [henergyY, hmu]
  have hminX : toHilbertBlockL2OfBlockField
      (scalar_cell_response_test_memL2 Q a hEll P) =
      M.toMuHilbertRealization.minimizerMap P :=
    R.recoveredField_minimizer_eq M P
  have hhilbert := hminX.trans hminY.symm
  have hXae : hilbertBlockL2ToBlockL2
      (toHilbertBlockL2OfBlockField
        (scalar_cell_response_test_memL2 Q a hEll P)) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      (fun x => X.eval x) := by
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField
        (scalar_cell_response_test_memL2 Q a hEll P),
      coeFn_hilbertBlockL2ToBlockL2
        (toHilbertBlockL2OfBlockField
          (scalar_cell_response_test_memL2 Q a hEll P))] with x hx hy
    rw [hy, hx]
    simp [X, hilbertifyBlockField]
  have hYae : hilbertBlockL2ToBlockL2
      (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      (fun x => Y.eval x) := by
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval,
      coeFn_hilbertBlockL2ToBlockL2
        (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval)] with x hx hy
    rw [hy, hx]
    simp [Y, hilbertifyBlockField]
  have hL2eq := congrArg hilbertBlockL2ToBlockL2 hhilbert
  filter_upwards [hXae, hYae] with x hx hy
  have h := congrArg (fun F : BlockL2 (openCubeSet Q) => F x) hL2eq
  rw [hx, hy] at h
  exact h

theorem main_quarterTurn_isSignedPermutation :
    IsSignedPermutationMatrix quarterTurn := by
  refine ⟨Equiv.swap 0 1, fun j => if j = 0 then 1 else -1, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [quarterTurn]

private theorem main_translateCoeffField_zero (a : CoeffField 2) :
    translateCoeffField (0 : Vec 2) a = a := by
  funext x
  ext i j
  simp [translateCoeffField]

theorem main_quarterTurnCellCoeff_originCube
    (m : ℤ) (a : CoeffField 2) :
    quarterTurnCellCoeff (originCube 2 m) a = rotateCoeffField quarterTurn a := by
  have hshift : triadicCubeShift (originCube 2 m) = 0 := by
    funext i
    simp [triadicCubeShift, originCube]
  have hmat : signFlipMatrix (0 : Fin 2) * Matrix.swap ℝ 0 1 = quarterTurn := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signFlipMatrix, quarterTurn, Matrix.mul_apply,
        Matrix.swap, Equiv.swap_apply_def, Fin.sum_univ_two]
  have htrans :
      matTranspose (Matrix.swap ℝ 0 1) *
          matTranspose (signFlipMatrix (0 : Fin 2)) =
        matTranspose (signFlipMatrix (0 : Fin 2) * Matrix.swap ℝ 0 1) := by
    simp [matTranspose, Matrix.transpose_mul]
  funext x
  change translateCoeffField (-triadicCubeShift (originCube 2 m))
      (rotateCoeffField (Matrix.swap ℝ 0 1)
        (rotateCoeffField (signFlipMatrix (0 : Fin 2))
          (translateCoeffField (triadicCubeShift (originCube 2 m)) a))) x =
    rotateCoeffField quarterTurn a x
  rw [hshift, neg_zero, main_translateCoeffField_zero]
  simp only [rotateCoeffField]
  rw [main_translateCoeffField_zero]
  calc
    matTranspose (Matrix.swap ℝ 0 1) *
        (matTranspose (signFlipMatrix (0 : Fin 2)) *
          a (matVecMul (signFlipMatrix (0 : Fin 2))
            (matVecMul (Matrix.swap ℝ 0 1) x)) *
          signFlipMatrix (0 : Fin 2)) * Matrix.swap ℝ 0 1 =
      matTranspose (signFlipMatrix (0 : Fin 2) * Matrix.swap ℝ 0 1) *
        a (matVecMul (signFlipMatrix (0 : Fin 2) * Matrix.swap ℝ 0 1) x) *
          (signFlipMatrix (0 : Fin 2) * Matrix.swap ℝ 0 1) := by
        rw [matVecMul_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc, htrans]
    _ = matTranspose quarterTurn * a (matVecMul quarterTurn x) *
        quarterTurn := by rw [hmat]

/-- Rotating the genuine cutoff sample rotates its actual partial-insertion
coefficient by the same signed-permutation action. -/
theorem main_partialInsertedCoefficient_rotateCutoffSample
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2)
    (R : Mat 2) (hR : IsSignedPermutationMatrix R) :
    Model.partialInsertedCoefficient M m t (rotateCutoffSample R hR ω) =
      Model.rotateCoefficientAbout (0 : Vec 2) R hR
        (Model.partialInsertedCoefficient M m t ω) := by
  have hforget (j : ShellField 2) :
      ShellField.forgetShell (ShellField.rotate R hR j) =
        rotateReg R hR (ShellField.forgetShell j) := by
    apply RegCoeffField.ext
    intro x
    simp [ShellField.rotate_apply, rotateReg_apply]
  rw [mainInsertion_coefficient, mainInsertion_coefficient]
  rw [Cutoff.coefficientCutoff_rotateCutoffSample]
  rw [Cutoff.rotateCutoffSample_val, ShellField.rotateSequence_apply, hforget]
  have hrotateAdd (a b : RegCoeffField 2) :
      rotateReg R hR (a + b) = rotateReg R hR a + rotateReg R hR b := by
    apply RegCoeffField.ext
    intro x
    ext i j
    simp [rotateReg_apply, RegCoeffField.add_apply, Matrix.mul_add,
      Matrix.add_mul]
  have hrotateSmul (c : ℝ) (a : RegCoeffField 2) :
      rotateReg R hR (c • a) = c • rotateReg R hR a := by
    apply RegCoeffField.ext
    intro x
    ext i j
    simp [rotateReg_apply, RegCoeffField.smul_apply, smul_eq_mul, mul_assoc]
  have hzero (a : RegCoeffField 2) :
      Model.rotateCoefficientAbout (0 : Vec 2) R hR a = rotateReg R hR a := by
    apply RegCoeffField.ext
    intro x
    simp [Model.rotateCoefficientAbout, translateReg_apply]
  rw [← hrotateSmul, ← hrotateAdd, hzero]

/-- The true OLD-frame coefficient on the source cell transforms by the
quarter-turn supplied by the actual cutoff-sample law. -/
theorem main_response_frame_coefficient_rotate_sample
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2)
    (x : Vec 2) (hx : x ∈ openCubeSet (originCube 2 (m - 5))) :
    responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t (originCube 2 (m - 5))
          (rotateCutoffSample quarterTurn main_quarterTurn_isSignedPermutation ω)) x =
      quarterTurnCellCoeff (originCube 2 (m - 5))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) x := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let R : Mat 2 := quarterTurn
  have hR_x : matVecMul R x = spatialQuarterTurn x := by
    ext i
    fin_cases i <;>
      simp [R, matVecMul, quarterTurn, spatialQuarterTurn,
        Fin.sum_univ_two]
  have hRx : matVecMul R x ∈ openCubeSet Q := by
    rw [hR_x]
    rw [mem_openCubeSet_originCube_iff] at hx ⊢
    intro i
    fin_cases i
    · have hcoord : spatialQuarterTurn x 0 = -x 1 := by
        simp [spatialQuarterTurn]
      change -(1 / 2 : ℝ) * 3 ^ (m - 5) < spatialQuarterTurn x 0 ∧
        spatialQuarterTurn x 0 < (1 / 2 : ℝ) * 3 ^ (m - 5)
      rw [hcoord]
      rcases hx 1 with ⟨hxlo, hxhi⟩
      constructor <;> linarith
    · have hcoord : spatialQuarterTurn x 1 = x 0 := by
        simp [spatialQuarterTurn]
      change -(1 / 2 : ℝ) * 3 ^ (m - 5) < spatialQuarterTurn x 1 ∧
        spatialQuarterTurn x 1 < (1 / 2 : ℝ) * 3 ^ (m - 5)
      rw [hcoord]
      exact hx 0
  have hR : IsSignedPermutationMatrix R := by
    simpa [R] using main_quarterTurn_isSignedPermutation
  have hpartial := main_partialInsertedCoefficient_rotateCutoffSample
    M m t ω R hR
  have hpartialx :
      Model.partialInsertedCoefficient M m t
          (rotateCutoffSample R hR ω) x =
        matTranspose R *
          (Model.partialInsertedCoefficient M m t ω) (matVecMul R x) * R := by
    calc
      Model.partialInsertedCoefficient M m t (rotateCutoffSample R hR ω) x =
          Model.rotateCoefficientAbout (0 : Vec 2) R hR
            (Model.partialInsertedCoefficient M m t ω) x := by
              exact congrArg (fun a : RegCoeffField 2 => a x) hpartial
      _ = matTranspose R *
          (Model.partialInsertedCoefficient M m t ω) (matVecMul R x) * R := by
            rw [Model.rotateCoefficientAbout_apply]
            simp
  have hframeRot := main_directional_response_frame_eq_scaled_partial_coefficient
    M m t Q (rotateCutoffSample R hR ω) x hx
  have hframeOrig := main_directional_response_frame_eq_scaled_partial_coefficient
    M m t Q ω (matVecMul R x) hRx
  calc
    responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t Q (rotateCutoffSample R hR ω)) x =
      (Annealed.sigmaBar M m : ℝ)⁻¹ •
        Model.partialInsertedCoefficient M m t (rotateCutoffSample R hR ω) x := hframeRot
    _ = (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (matTranspose R * (Model.partialInsertedCoefficient M m t ω)
          (matVecMul R x) * R) := by rw [hpartialx]
    _ = matTranspose R *
        ((Annealed.sigmaBar M m : ℝ)⁻¹ •
          (Model.partialInsertedCoefficient M m t ω) (matVecMul R x)) * R := by
          ext i j
          simp [Matrix.smul_apply, smul_eq_mul]
    _ = matTranspose R *
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t Q ω) (matVecMul R x)) * R := by
          rw [← hframeOrig]
    _ = rotateCoeffField R
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t Q ω)) x := rfl
    _ = quarterTurnCellCoeff Q
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t Q ω)) x := by
          exact (congrFun (main_quarterTurnCellCoeff_originCube
            (m - 5) (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainInsertionSkewCoefficient m t Q ω))).symm x)

/-- The actual OLD-frame minimizer for a quarter-turned cutoff sample agrees
with the cell-symmetry transform of the original minimizer. The only bridge
between the actual sample coefficient and the symmetry coefficient is their
proved equality on the open source cell. -/
theorem main_old_signed_frame_quarterTurn_minimizer_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2)
    (P : BlockVec 2) :
    oldSignedFrameCanonicalField (originCube 2 (m - 5)) M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
      (mainInsertionSkewCoefficient m t (originCube 2 (m - 5))
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω))
      (quarterTurnLoad P) =ᵐ[
        volumeMeasureOn (openCubeSet (originCube 2 (m - 5)))]
      (quarterTurnCellState (originCube 2 (m - 5))
        (scalarCellResponseTest (originCube 2 (m - 5))
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω))
          (responseFramePlanarCoefficientField_isElliptic
            (measurableSet_openCubeSet (originCube 2 (m - 5))) M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos
            (Annealed.sigmaBar M m).2
            (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω))
          P)).eval := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let kRot := mainInsertionSkewCoefficient m t Q
    (rotateCutoffSample quarterTurn
      main_quarterTurn_isSignedPermutation ω)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let aRot := responseFramePlanarCoefficientField M.nu σ kRot
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos (Annealed.sigmaBar M m).2 k
  let hEllRot := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos (Annealed.sigmaBar M m).2 kRot
  let hEllSymm := quarterTurnCellCoeff_isElliptic Q a hEll
  have hCoeff : aRot =ᵐ[volumeMeasureOn (openCubeSet Q)]
      quarterTurnCellCoeff Q a := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact main_response_frame_coefficient_rotate_sample M m t ω x hx
  have hTest := main_scalarCellResponseTest_congr_coeff_ae
    Q aRot (quarterTurnCellCoeff Q a) hEllRot hEllSymm hCoeff
      (quarterTurnLoad P)
  have hQuarter := scalar_cell_response_test_centered_quarterTurn_ae
    Q a hEll P
  have hCanonical : oldSignedFrameCanonicalField Q M.nu σ
      M.nu_pos (Annealed.sigmaBar M m).2 kRot (quarterTurnLoad P) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q aRot hEllRot
        (quarterTurnLoad P)).eval := by
    simpa [oldSignedFrameCanonicalField, aRot, hEllRot] using
      (old_signed_canonical_affine_field_recovery Q aRot hEllRot
        (quarterTurnLoad P))
  filter_upwards [hCanonical, hTest, hQuarter] with x hcan hcoef hturn
  exact hcan.trans (hcoef.trans hturn)

/-- On an origin square, the recovered cell-state action is the usual spatial
quarter turn together with its contragredient action on vector components. -/
theorem main_quarterTurnCellState_eval_originCube
    (m : ℤ) (X : BlockState 2) (x : Vec 2) :
    (quarterTurnCellState (originCube 2 m) X).eval x =
      blockVecConj (matTranspose quarterTurn)
        (X.eval (spatialQuarterTurn x)) := by
  have hshift : triadicCubeShift (originCube 2 m) = 0 := by
    funext i
    simp [triadicCubeShift, originCube]
  have hmatrixIn : signFlipMatrix (0 : Fin 2) * Matrix.swap ℝ 0 1 =
      quarterTurn := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signFlipMatrix, quarterTurn, Matrix.mul_apply,
        Matrix.swap, Equiv.swap_apply_def, Fin.sum_univ_two]
  have houtput : Matrix.swap ℝ 0 1 * signFlipMatrix (0 : Fin 2) =
      matTranspose quarterTurn := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signFlipMatrix, matTranspose, quarterTurn,
        Matrix.mul_apply, Matrix.swap, Equiv.swap_apply_def,
        Fin.sum_univ_two]
  have hinput (y : Vec 2) : matVecMul quarterTurn y =
      spatialQuarterTurn y := by
    ext i
    fin_cases i <;>
      simp [matVecMul, quarterTurn, spatialQuarterTurn,
        Fin.sum_univ_two]
  have hcomp (v : Vec 2) :
      matVecMul (Matrix.swap ℝ 0 1)
          (matVecMul (signFlipMatrix (0 : Fin 2)) v) =
        matVecMul (matTranspose quarterTurn) v := by
    rw [matVecMul_mul, houtput]
  rw [quarterTurnCellState, hshift, neg_zero]
  simp only [BlockState.translate, sub_zero, BlockState.eval,
    BlockState.swap, BlockState.signFlip,
    swapVecContinuousLinearEquiv_apply,
    signFlipVecContinuousLinearEquiv_apply]
  change (matVecMul (Matrix.swap ℝ 0 1)
      (matVecMul (signFlipMatrix (0 : Fin 2))
        (X.potential (matVecMul (signFlipMatrix (0 : Fin 2))
          (matVecMul (Matrix.swap ℝ 0 1) x)))),
    matVecMul (Matrix.swap ℝ 0 1)
      (matVecMul (signFlipMatrix (0 : Fin 2))
        (X.flux (matVecMul (signFlipMatrix (0 : Fin 2))
          (matVecMul (Matrix.swap ℝ 0 1) x))))) =
      (matVecMul (matTranspose quarterTurn)
          (X.potential (spatialQuarterTurn x)),
        matVecMul (matTranspose quarterTurn)
          (X.flux (spatialQuarterTurn x)))
  rw [hcomp, hcomp, matVecMul_mul, hmatrixIn, hinput]

private theorem main_dualEnergy_neg
    (Q : TriadicCube 2) (f : Vec 2 → ℝ) :
    dualEnergy Q (Real.sqrt 3) (fun x => -f x) =
      dualEnergy Q (Real.sqrt 3) f := by
  unfold dualEnergy
  exact primalEnergy_neg Q (Real.sqrt 3)⁻¹ f

/-- The exact order-1/4 weak-Haar energy is invariant under the joint
quarter-turn of space and vector components furnished by the cell symmetry. -/
theorem main_vectorWeakHaarEnergy_quarterTurnFrame
    (m : ℤ) (F : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2
      (normalizedCubeMeasure (originCube 2 m))) :
    vectorWeakHaarEnergy (originCube 2 m)
        (fun x i => matVecMul (matTranspose quarterTurn)
          (F (spatialQuarterTurn x)) i) =
      vectorWeakHaarEnergy (originCube 2 m) F := by
  have hcomponents :
      vectorWeakHaarEnergy (originCube 2 m)
          (fun x i => matVecMul (matTranspose quarterTurn)
            (F (spatialQuarterTurn x)) i) =
        vectorWeakHaarEnergy (originCube 2 m)
          (fun x i => F (spatialQuarterTurn x) i) := by
    unfold vectorWeakHaarEnergy
    simp only [Fin.sum_univ_two]
    simp [matTranspose, matVecMul, quarterTurn,
      Matrix.transpose_apply, Fin.sum_univ_two,
      main_dualEnergy_neg]
    ring
  exact hcomponents.trans
    (vectorWeakHaarEnergy_spatialQuarterTurn m F hF)

private theorem main_directional_raw_ae_to_cube_ae
    (Q : TriadicCube 2) {P : Vec 2 → Prop}
    (hP : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), P x) :
    ∀ᵐ x ∂volume.restrict (cubeSet Q), P x := by
  rw [volumeMeasureOn, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at hP
  exact hP

private theorem main_vectorWeakHaarEnergy_congr_ae
    (Q : TriadicCube 2) {F G : Vec 2 → Fin 2 → ℝ}
    (hFG : F =ᵐ[volume.restrict (cubeSet Q)] G) :
    vectorWeakHaarEnergy Q F = vectorWeakHaarEnergy Q G := by
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  have hcoord : (fun x => F x i) =ᵐ[volume.restrict (cubeSet Q)]
      (fun x => G x i) := by
    filter_upwards [hFG] with x hx
    exact congrFun hx i
  unfold dualEnergy
  exact diagPrimalEnergy_congr_ae Q (Real.sqrt 3)⁻¹ hcoord

/-- The first-coordinate weak-Haar energy of the actual OLD canonical
minimizer is covariant under the actual quarter-turned cutoff sample. -/
theorem main_old_signed_frame_first_weak_energy_quarterTurn
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2)
    (P : BlockVec 2) :
    vectorWeakHaarEnergy (originCube 2 (m - 5))
      (fun x i => (oldSignedFrameCanonicalField
        (originCube 2 (m - 5)) M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t (originCube 2 (m - 5))
          (rotateCutoffSample quarterTurn
            main_quarterTurn_isSignedPermutation ω))
        (quarterTurnLoad P) x).1 i - (quarterTurnLoad P).1 i) =
      vectorWeakHaarEnergy (originCube 2 (m - 5))
        (fun x i => (oldSignedFrameCanonicalField
          (originCube 2 (m - 5)) M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)
          P x).1 i - P.1 i) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos (Annealed.sigmaBar M m).2 k
  let F : Vec 2 → Fin 2 → ℝ := fun x i =>
    ((scalarCellResponseTest Q a hEll P).eval x - P).1 i
  have hRecovery : oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).2 k P =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q a hEll P).eval := by
    simpa [oldSignedFrameCanonicalField, a, hEll] using
      (old_signed_canonical_affine_field_recovery Q a hEll P)
  have hOriginal :
      (fun x i => (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).2 k P x).1 i - P.1 i) =ᵐ[
          volumeMeasureOn (openCubeSet Q)] F := by
    filter_upwards [hRecovery] with x hx
    have hfirst := congrArg Prod.fst hx
    have hsub := congrArg (fun v : Vec 2 => v - P.1) hfirst
    exact hsub
  have hTestDiff : MemBlockL2 (openCubeSet Q)
      (fun x => (scalarCellResponseTest Q a hEll P).eval x - P) :=
    (scalar_cell_response_test_variation Q a hEll P).1
  have hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2
        (memVectorL2_fst_of_memBlockL2
          hTestDiff) i)
  have hMin := main_old_signed_frame_quarterTurn_minimizer_ae
    M m t ω P
  have hLoad : quarterTurnLoad P = blockVecConj
      (matTranspose quarterTurn) P := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [quarterTurnLoad, blockVecConj, matVecMul,
        matTranspose, signFlipMatrix, Matrix.swap, quarterTurn,
        Fin.sum_univ_two]
  have hLinear (u v : Vec 2) :
      matVecMul (matTranspose quarterTurn) u -
          matVecMul (matTranspose quarterTurn) v =
        matVecMul (matTranspose quarterTurn) (u - v) := by
    calc
      _ = matVecMul (matTranspose quarterTurn) u +
          matVecMul (matTranspose quarterTurn) (-v) := by
            rw [matVecMul_neg]
            rfl
      _ = matVecMul (matTranspose quarterTurn) (u + -v) :=
            (matVecMul_add _ _ _).symm
      _ = _ := by rw [sub_eq_add_neg]
  have hRotated :
      (fun x i => (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q
          (rotateCutoffSample quarterTurn
            main_quarterTurn_isSignedPermutation ω))
        (quarterTurnLoad P) x).1 i - (quarterTurnLoad P).1 i) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        (fun x i => matVecMul (matTranspose quarterTurn)
          (((scalarCellResponseTest Q a hEll P).eval
            (spatialQuarterTurn x) - P).1) i) := by
    filter_upwards [hMin] with x hx
    have hstate := congrArg Prod.fst hx
    rw [main_quarterTurnCellState_eval_originCube
      (m - 5) (scalarCellResponseTest Q a hEll P) x] at hstate
    funext i
    have hfield := congrFun hstate i
    have hload := congrFun (congrArg Prod.fst hLoad) i
    rw [hfield, hload]
    exact congrFun (hLinear
      ((scalarCellResponseTest Q a hEll P).eval
        (spatialQuarterTurn x)).1 P.1) i
  have hOriginalCube := main_directional_raw_ae_to_cube_ae Q hOriginal
  have hRotatedCube := main_directional_raw_ae_to_cube_ae Q hRotated
  have hRotEnergy := main_vectorWeakHaarEnergy_congr_ae Q hRotatedCube
  have hFrameEnergy := main_vectorWeakHaarEnergy_quarterTurnFrame
    (m - 5) F hF
  have hOriginalEnergy := main_vectorWeakHaarEnergy_congr_ae Q hOriginalCube
  exact hRotEnergy.trans (hFrameEnergy.trans hOriginalEnergy.symm)

private theorem main_quarterTurn_matrix_products :
    signFlipMatrix (0 : Fin 2) * Matrix.swap ℝ 0 1 = quarterTurn ∧
      Matrix.swap ℝ 0 1 * signFlipMatrix (0 : Fin 2) =
        matTranspose quarterTurn := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signFlipMatrix, quarterTurn, Matrix.mul_apply,
        Matrix.swap, Equiv.swap_apply_def, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signFlipMatrix, matTranspose, quarterTurn,
        Matrix.mul_apply, Matrix.swap, Equiv.swap_apply_def,
        Fin.sum_univ_two]

private theorem main_quarterTurn_matrix_apply (x : Vec 2) :
    matVecMul quarterTurn x = spatialQuarterTurn x := by
  ext i
  fin_cases i <;>
    simp [matVecMul, quarterTurn, spatialQuarterTurn,
      Fin.sum_univ_two]

private theorem main_quarterTurn_originCube (m : ℤ) :
    quarterTurnCube (originCube 2 m) = originCube 2 m := by
  have hExt : ∀ {A B : TriadicCube 2}, A.scale = B.scale →
      A.index = B.index → A = B := by
    intro A B hs hi
    cases A
    cases B
    simp_all
  apply hExt
  · rfl
  · funext i
    fin_cases i <;> simp [quarterTurnCube, originCube]

private theorem main_spatialQuarterTurn_openMeasurePreserving (m : ℤ) :
    MeasurePreserving spatialQuarterTurn
      (volumeMeasureOn (openCubeSet (originCube 2 m)))
      (volumeMeasureOn (openCubeSet (originCube 2 m))) := by
  let Q : TriadicCube 2 := originCube 2 m
  have hfun : (spatialQuarterTurnEquiv.toHomeomorph : Vec 2 → Vec 2) =
      spatialQuarterTurn := by
    funext x
    exact spatialQuarterTurnEquiv_apply x
  have hEmb : MeasurableEmbedding spatialQuarterTurn := by
    simpa only [hfun] using
      spatialQuarterTurnEquiv.toHomeomorph.measurableEmbedding
  have hpre : spatialQuarterTurn ⁻¹' openCubeSet Q = openCubeSet Q := by
    calc
      spatialQuarterTurn ⁻¹' openCubeSet Q =
          spatialQuarterTurn ⁻¹'
            openCubeSet (quarterTurnCube Q) := by
              rw [main_quarterTurn_originCube m]
      _ = openCubeSet Q := spatialQuarterTurn_openCubeSet Q
  have hμ := spatialQuarterTurn_measurePreserving.restrict_preimage_emb
    hEmb (openCubeSet Q)
  simpa only [volumeMeasureOn, Q, hpre] using hμ

private theorem main_blockMatrixOfCoeff_quarterTurnCellCoeff
    (m : ℤ) (a : CoeffField 2) (x : Vec 2) :
    blockMatrixOfCoeff (quarterTurnCellCoeff (originCube 2 m) a x) =
      blockMatConj (Matrix.swap ℝ 0 1)
        (blockMatConj (signFlipMatrix 0)
          (blockMatrixOfCoeff (a (spatialQuarterTurn x)))) := by
  let W : Mat 2 := Matrix.swap ℝ 0 1
  let S : Mat 2 := signFlipMatrix 0
  have hProducts := main_quarterTurn_matrix_products
  have hW : matTranspose W = W := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [W, matTranspose, Matrix.swap]
  have hS : matTranspose S = S := by
    simpa [S] using matTranspose_signFlipMatrix (0 : Fin 2)
  have hcoeff : quarterTurnCellCoeff (originCube 2 m) a x =
      W * (S * a (spatialQuarterTurn x) * S) * W := by
    calc
      quarterTurnCellCoeff (originCube 2 m) a x =
          rotateCoeffField quarterTurn a x := by
            exact congrFun (main_quarterTurnCellCoeff_originCube m a) x
      _ = matTranspose quarterTurn *
          a (matVecMul quarterTurn x) * quarterTurn := rfl
      _ = (W * S) * a (spatialQuarterTurn x) * (S * W) := by
            rw [hProducts.2, main_quarterTurn_matrix_apply,
              hProducts.1]
      _ = W * (S * a (spatialQuarterTurn x) * S) * W := by
            simp only [Matrix.mul_assoc]
  rw [hcoeff]
  calc
    blockMatrixOfCoeff
        (W * (S * a (spatialQuarterTurn x) * S) * W) =
        blockMatConj W
          (blockMatrixOfCoeff (S * a (spatialQuarterTurn x) * S)) := by
            simpa [W] using blockMatrixOfCoeff_swap_conj (0 : Fin 2) 1
              (S * a (spatialQuarterTurn x) * S)
    _ = blockMatConj W
        (blockMatConj S
          (blockMatrixOfCoeff (a (spatialQuarterTurn x)))) := by
            rw [blockMatrixOfCoeff_signFlipMatrix_conj]

private theorem main_blockVecConj_quarterTurn_comp
    (X : BlockVec 2) :
    blockVecConj (Matrix.swap ℝ 0 1)
        (blockVecConj (signFlipMatrix 0) X) =
      blockVecConj (matTranspose quarterTurn) X := by
  rcases X with ⟨u, v⟩
  have hProducts := main_quarterTurn_matrix_products
  simp only [blockVecConj]
  rw [matVecMul_mul, hProducts.2, matVecMul_mul, hProducts.2]

private theorem main_blockMatVecMul_quarterTurnCellCoeff
    (m : ℤ) (a : CoeffField 2) (x : Vec 2) (X : BlockVec 2) :
    blockMatVecMul
        (blockMatrixOfCoeff (quarterTurnCellCoeff (originCube 2 m) a x))
        (blockVecConj (matTranspose quarterTurn) X) =
      blockVecConj (matTranspose quarterTurn)
        (blockMatVecMul (blockMatrixOfCoeff (a (spatialQuarterTurn x))) X) := by
  let W : Mat 2 := Matrix.swap ℝ 0 1
  let S : Mat 2 := signFlipMatrix 0
  let B := blockMatrixOfCoeff (a (spatialQuarterTurn x))
  have hMatrix := main_blockMatrixOfCoeff_quarterTurnCellCoeff m a x
  have hComp := main_blockVecConj_quarterTurn_comp X
  have hW2 : W * W = 1 := by
    simpa [W] using (Matrix.swap_mul_self (R := ℝ) (0 : Fin 2) 1)
  have hS2 : S * S = 1 := by
    simpa [S] using signFlipMatrix_mul_self (0 : Fin 2)
  calc
    blockMatVecMul
        (blockMatrixOfCoeff (quarterTurnCellCoeff (originCube 2 m) a x))
        (blockVecConj (matTranspose quarterTurn) X) =
      blockMatVecMul (blockMatConj W (blockMatConj S B))
        (blockVecConj W (blockVecConj S X)) := by
          rw [hMatrix, ← hComp]
    _ = blockVecConj W
        (blockMatVecMul (blockMatConj S B) (blockVecConj S X)) :=
          blockMatVecMul_blockMatConj_of_mul_self_eq_one hW2
            (blockMatConj S B) (blockVecConj S X)
    _ = blockVecConj W (blockVecConj S (blockMatVecMul B X)) := by
          rw [blockMatVecMul_blockMatConj_of_mul_self_eq_one hS2 B X]
    _ = blockVecConj (matTranspose quarterTurn)
        (blockMatVecMul B X) :=
          main_blockVecConj_quarterTurn_comp (blockMatVecMul B X)

/-- The actual OLD coefficient dual reflection transforms with the same
quarter-turn as the canonical minimizer. The coefficient action is the exact
cell rotation, and the state action is compared through the established
minimizer covariance and its recovery representative. -/
theorem main_old_signed_dual_reflection_quarterTurn_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2)
    (P : BlockVec 2) :
    oldSignedDualReflection (originCube 2 (m - 5)) M.nu
        (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t (originCube 2 (m - 5))
          (rotateCutoffSample quarterTurn
            main_quarterTurn_isSignedPermutation ω))
        (oldSignedFrameCanonicalField (originCube 2 (m - 5)) M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t (originCube 2 (m - 5))
            (rotateCutoffSample quarterTurn
              main_quarterTurn_isSignedPermutation ω))
          (quarterTurnLoad P)) =ᵐ[
            volumeMeasureOn (openCubeSet (originCube 2 (m - 5)))]
      (fun x => blockVecConj (matTranspose quarterTurn)
        (oldSignedDualReflection (originCube 2 (m - 5)) M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)
          (oldSignedFrameCanonicalField (originCube 2 (m - 5)) M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
            (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)
            P) (spatialQuarterTurn x))) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let kRot := mainInsertionSkewCoefficient m t Q
    (rotateCutoffSample quarterTurn
      main_quarterTurn_isSignedPermutation ω)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let aRot := responseFramePlanarCoefficientField M.nu σ kRot
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos (Annealed.sigmaBar M m).2 k
  have hCoeff : aRot =ᵐ[volumeMeasureOn (openCubeSet Q)]
      quarterTurnCellCoeff Q a := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact main_response_frame_coefficient_rotate_sample M m t ω x hx
  have hMin := main_old_signed_frame_quarterTurn_minimizer_ae
    M m t ω P
  have hRecovery : oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).2 k P =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q a hEll P).eval := by
    simpa [oldSignedFrameCanonicalField, a, hEll] using
      (old_signed_canonical_affine_field_recovery Q a hEll P)
  have hmp := main_spatialQuarterTurn_openMeasurePreserving (m - 5)
  have hRecoveryComp := hmp.quasiMeasurePreserving.ae_eq_comp hRecovery
  filter_upwards [hCoeff, hMin, hRecoveryComp,
    ae_restrict_mem (measurableSet_openCubeSet Q)] with x hCoeffX hMinX hRecX hx
  let X := (scalarCellResponseTest Q a hEll P).eval (spatialQuarterTurn x)
  have hState :
      oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).2 kRot (quarterTurnLoad P) x =
        blockVecConj (matTranspose quarterTurn) X := by
    rw [hMinX, main_quarterTurnCellState_eval_originCube
      (m - 5) (scalarCellResponseTest Q a hEll P) x]
  have hOriginal :
      oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).2 k P (spatialQuarterTurn x) = X := by
    simpa [X, Function.comp_apply] using hRecX
  have hMatrix := main_blockMatVecMul_quarterTurnCellCoeff
    (m - 5) a x X
  have hConjSwap (Y : BlockVec 2) :
      (blockVecConj (matTranspose quarterTurn) Y).swap =
        blockVecConj (matTranspose quarterTurn) Y.swap := by
    rcases Y with ⟨u, v⟩
    rfl
  have hSwap := congrArg Prod.swap hMatrix
  have hGoal := hSwap.trans (hConjSwap _)
  rw [← hCoeffX, ← hState, ← hOriginal] at hGoal
  simpa [oldSignedDualReflection, blockCoeffField, Q, σ, k, kRot] using hGoal

/-- The actual reciprocal bottom-load weak energy is invariant under the
quarter-turn of the cutoff sample and its physical direction. -/
theorem main_old_signed_bottom_reciprocal_weak_energy_quarterTurn
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) (e : Vec 2) :
    vectorWeakHaarEnergy (originCube 2 (m - 5))
      (fun x i => mainDirectionalBottomReciprocalDirection M m t
        (originCube 2 (m - 5))
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω)
        (matVecMul (matTranspose quarterTurn) e) x i) =
    vectorWeakHaarEnergy (originCube 2 (m - 5))
      (fun x i => mainDirectionalBottomReciprocalDirection M m t
        (originCube 2 (m - 5)) ω e x i) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let R : Mat 2 := quarterTurn
  let P : BlockVec 2 := (0, e)
  let F : Vec 2 → Fin 2 → ℝ := fun x i =>
    mainDirectionalBottomReciprocalDirection M m t Q ω e x i
  have hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact main_directional_bottom_reciprocal_direction_memLp M m t Q ω e i
  have hLoad : quarterTurnLoad P =
      (0, matVecMul (matTranspose quarterTurn) e) := by
    apply Prod.ext
    · ext i
      fin_cases i <;>
        simp [P, quarterTurnLoad, blockVecConj, matVecMul,
          matTranspose, signFlipMatrix, Matrix.swap, quarterTurn,
          Fin.sum_univ_two]
    · ext i
      fin_cases i <;>
        simp [P, quarterTurnLoad, blockVecConj, matVecMul,
          matTranspose, signFlipMatrix, Matrix.swap, quarterTurn,
          Fin.sum_univ_two]
  have hLinear (u v : Vec 2) :
      matVecMul (matTranspose quarterTurn) u -
          matVecMul (matTranspose quarterTurn) v =
        matVecMul (matTranspose quarterTurn) (u - v) := by
    calc
      _ = matVecMul (matTranspose quarterTurn) u +
          matVecMul (matTranspose quarterTurn) (-v) := by
            rw [matVecMul_neg]
            rfl
      _ = matVecMul (matTranspose quarterTurn) (u + -v) :=
            (matVecMul_add _ _ _).symm
      _ = _ := by rw [sub_eq_add_neg]
  have hDual := main_old_signed_dual_reflection_quarterTurn_ae
    M m t ω P
  have hDirection :
      (fun x i => mainDirectionalBottomReciprocalDirection M m t Q
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω)
        (matVecMul (matTranspose quarterTurn) e) x i) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      (fun x i => matVecMul (matTranspose quarterTurn)
        (mainDirectionalBottomReciprocalDirection M m t Q ω e
          (spatialQuarterTurn x)) i) := by
    unfold mainDirectionalBottomReciprocalDirection
    filter_upwards [hDual] with x hDualX
    rw [hLoad] at hDualX
    have hFirst := congrArg Prod.fst hDualX
    have hFirst' :
        (oldSignedDualReflection Q M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t Q
            (rotateCutoffSample quarterTurn
              main_quarterTurn_isSignedPermutation ω))
          (oldSignedFrameCanonicalField Q M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos
            (Annealed.sigmaBar M m).2
            (mainInsertionSkewCoefficient m t Q
              (rotateCutoffSample quarterTurn
                main_quarterTurn_isSignedPermutation ω))
            (0, matVecMul (matTranspose quarterTurn) e)) x).1 =
          matVecMul (matTranspose quarterTurn)
            ((oldSignedDualReflection Q M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainInsertionSkewCoefficient m t Q ω)
              (oldSignedFrameCanonicalField Q M.nu
                (Annealed.sigmaBar M m : ℝ) M.nu_pos
                (Annealed.sigmaBar M m).2
                (mainInsertionSkewCoefficient m t Q ω) P)
              (spatialQuarterTurn x)).1) := by
      simpa [blockVecConj] using hFirst
    have hVector :
        (oldSignedDualReflection Q M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t Q
          (rotateCutoffSample quarterTurn
            main_quarterTurn_isSignedPermutation ω))
        (oldSignedFrameCanonicalField Q M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t Q
            (rotateCutoffSample quarterTurn
              main_quarterTurn_isSignedPermutation ω))
          (0, matVecMul (matTranspose quarterTurn) e)) x).1 -
        matVecMul (matTranspose quarterTurn) e =
      matVecMul (matTranspose quarterTurn)
        ((oldSignedDualReflection Q M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t Q ω)
        (oldSignedFrameCanonicalField Q M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t Q ω) P)
        (spatialQuarterTurn x)).1 - e) := by
      calc
        _ = matVecMul (matTranspose quarterTurn)
              ((oldSignedDualReflection Q M.nu
                (Annealed.sigmaBar M m : ℝ)
                (mainInsertionSkewCoefficient m t Q ω)
                (oldSignedFrameCanonicalField Q M.nu
                  (Annealed.sigmaBar M m : ℝ) M.nu_pos
                  (Annealed.sigmaBar M m).2
                  (mainInsertionSkewCoefficient m t Q ω) P)
                (spatialQuarterTurn x)).1) -
              matVecMul (matTranspose quarterTurn) e := by
                rw [hFirst']
        _ = matVecMul (matTranspose quarterTurn)
              ((oldSignedDualReflection Q M.nu
                (Annealed.sigmaBar M m : ℝ)
                (mainInsertionSkewCoefficient m t Q ω)
                (oldSignedFrameCanonicalField Q M.nu
                  (Annealed.sigmaBar M m : ℝ) M.nu_pos
                  (Annealed.sigmaBar M m).2
                  (mainInsertionSkewCoefficient m t Q ω) P)
                (spatialQuarterTurn x)).1 - e) := hLinear _ _
    funext i
    exact congrFun hVector i
  have hDirectionCube := main_directional_raw_ae_to_cube_ae Q hDirection
  have hRotEnergy := main_vectorWeakHaarEnergy_congr_ae Q hDirectionCube
  have hFrameEnergy := main_vectorWeakHaarEnergy_quarterTurnFrame
    (m - 5) F hF
  exact hRotEnergy.trans hFrameEnergy

private theorem main_quarterTurnLoad_components (P : BlockVec 2) :
    quarterTurnLoad P =
      (matVecMul (matTranspose quarterTurn) P.1,
        matVecMul (matTranspose quarterTurn) P.2) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [quarterTurnLoad, blockVecConj, matVecMul,
      matTranspose, signFlipMatrix, Matrix.swap, quarterTurn,
      Fin.sum_univ_two]

private theorem main_quarterTurn_isometry_id (e : Vec 2) :
    matVecMul (matTranspose quarterTurn)
      (matVecMul quarterTurn e) = e := by
  ext i
  fin_cases i <;>
    simp [matVecMul, matTranspose, quarterTurn, Fin.sum_univ_two]

private theorem main_old_signed_frame_quarterTurn_state_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2)
    (P : BlockVec 2) :
    oldSignedFrameCanonicalField (originCube 2 (m - 5)) M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t (originCube 2 (m - 5))
          (rotateCutoffSample quarterTurn
            main_quarterTurn_isSignedPermutation ω))
        (quarterTurnLoad P) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 (m - 5)))]
      fun x => blockVecConj (matTranspose quarterTurn)
        (oldSignedFrameCanonicalField (originCube 2 (m - 5)) M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)
          P (spatialQuarterTurn x)) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
    (Annealed.sigmaBar M m).2 k
  have hMin := main_old_signed_frame_quarterTurn_minimizer_ae
    M m t ω P
  have hRecovery : oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).2 k P =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q a hEll P).eval := by
    simpa [oldSignedFrameCanonicalField, a, hEll] using
      (old_signed_canonical_affine_field_recovery Q a hEll P)
  have hmp := main_spatialQuarterTurn_openMeasurePreserving (m - 5)
  have hRecoveryComp := hmp.quasiMeasurePreserving.ae_eq_comp hRecovery
  filter_upwards [hMin, hRecoveryComp] with x hMinX hRecoveryX
  rw [main_quarterTurnCellState_eval_originCube (m - 5)] at hMinX
  have hRecoveryPoint : oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).2 k P (spatialQuarterTurn x) =
      (scalarCellResponseTest Q a hEll P).eval (spatialQuarterTurn x) := by
    simpa [Function.comp_apply] using hRecoveryX
  rw [← hRecoveryPoint] at hMinX
  exact hMinX

/-- The actual top physical-flux weak energy is covariant under the actual
quarter-turn of the cutoff sample and its physical direction. -/
theorem main_directional_top_physical_flux_weak_energy_quarterTurn
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) (e : Vec 2) :
    vectorWeakHaarEnergy (originCube 2 (m - 5))
      (mainDirectionalTopPhysicalFluxDirectionError M m t
        (originCube 2 (m - 5))
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω) e) =
    vectorWeakHaarEnergy (originCube 2 (m - 5))
      (mainDirectionalTopPhysicalFluxDirectionError M m t
        (originCube 2 (m - 5)) ω (matVecMul quarterTurn e)) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let R : Mat 2 := quarterTurn
  let P : BlockVec 2 := (matVecMul R e, 0)
  let F : Vec 2 → Fin 2 → ℝ := fun x i =>
    mainDirectionalTopPhysicalFluxDirectionError M m t Q ω
      (matVecMul R e) x i
  have hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact main_directional_top_physical_flux_direction_memLp
      M m t Q ω (matVecMul R e) i
  have hRe : matVecMul (matTranspose R) (matVecMul R e) = e := by
    simpa [R] using main_quarterTurn_isometry_id e
  have hLoad : quarterTurnLoad P = (e, 0) := by
    rw [main_quarterTurnLoad_components]
    apply Prod.ext
    · exact hRe
    · ext i
      simp [P, matVecMul]
  have hState := main_old_signed_frame_quarterTurn_state_ae
    M m t ω P
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ)
    (mainInsertionSkewCoefficient m t Q ω)
  let aRot : CoeffField 2 := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ)
    (mainInsertionSkewCoefficient m t Q
      (rotateCutoffSample quarterTurn
        main_quarterTurn_isSignedPermutation ω))
  have hCoeff : aRot =ᵐ[volumeMeasureOn (openCubeSet Q)]
      quarterTurnCellCoeff Q a := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact main_response_frame_coefficient_rotate_sample M m t ω x hx
  have hLinear (u v : Vec 2) :
      matVecMul (matTranspose R) u - matVecMul (matTranspose R) v =
        matVecMul (matTranspose R) (u - v) := by
    calc
      _ = matVecMul (matTranspose R) u +
          matVecMul (matTranspose R) (-v) := by
            rw [matVecMul_neg]
            rfl
      _ = matVecMul (matTranspose R) (u + -v) :=
        (matVecMul_add _ _ _).symm
      _ = _ := by rw [sub_eq_add_neg]
  have hDirection :
      (fun x i => mainDirectionalTopPhysicalFluxDirectionError
        M m t Q
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω) e x i) =ᵐ[
            volumeMeasureOn (openCubeSet Q)]
      (fun x i => matVecMul (matTranspose R)
        (mainDirectionalTopPhysicalFluxDirectionError M m t Q ω
          (matVecMul R e) (spatialQuarterTurn x)) i) := by
    filter_upwards [hCoeff, hState,
      ae_restrict_mem (measurableSet_openCubeSet Q)] with x hCoeffX hStateX hx
    rw [hLoad] at hStateX
    unfold mainDirectionalTopPhysicalFluxDirectionError
    have hFlux := main_blockMatVecMul_quarterTurnCellCoeff
      (m - 5) a x
      (oldSignedFrameCanonicalField Q M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) P
        (spatialQuarterTurn x))
    have hFlux' := congrArg Prod.fst hFlux
    have hFlux'' :
        (blockMatVecMul
          (blockMatrixOfCoeff (quarterTurnCellCoeff Q a x))
          (blockVecConj (matTranspose quarterTurn)
            (oldSignedFrameCanonicalField Q M.nu
              (Annealed.sigmaBar M m : ℝ) M.nu_pos
              (Annealed.sigmaBar M m).2
              (mainInsertionSkewCoefficient m t Q ω) P
              (spatialQuarterTurn x)))).1 =
        matVecMul (matTranspose R)
          ((blockMatVecMul
            (blockMatrixOfCoeff (a (spatialQuarterTurn x)))
            (oldSignedFrameCanonicalField Q M.nu
              (Annealed.sigmaBar M m : ℝ) M.nu_pos
              (Annealed.sigmaBar M m).2
              (mainInsertionSkewCoefficient m t Q ω) P
              (spatialQuarterTurn x))).1) := by
      simpa [R, blockVecConj] using hFlux'
    have hCoeffMatrix : blockCoeffField aRot x =
        blockMatrixOfCoeff (quarterTurnCellCoeff Q a x) := by
      change blockMatrixOfCoeff (aRot x) = _
      rw [hCoeffX]
    have hCoeffOrig : blockCoeffField a (spatialQuarterTurn x) =
        blockMatrixOfCoeff (a (spatialQuarterTurn x)) := rfl
    have hVector :
        (blockMatVecMul (blockCoeffField aRot x)
          (oldSignedFrameCanonicalField Q M.nu
            (Annealed.sigmaBar M m : ℝ) M.nu_pos
            (Annealed.sigmaBar M m).2
            (mainInsertionSkewCoefficient m t Q
              (rotateCutoffSample quarterTurn
                main_quarterTurn_isSignedPermutation ω))
            (e, 0) x)).1 - e =
        matVecMul (matTranspose R)
          ((blockMatVecMul (blockCoeffField a (spatialQuarterTurn x))
            (oldSignedFrameCanonicalField Q M.nu
              (Annealed.sigmaBar M m : ℝ) M.nu_pos
              (Annealed.sigmaBar M m).2
              (mainInsertionSkewCoefficient m t Q ω) P
              (spatialQuarterTurn x))).1 - matVecMul R e) := by
      rw [hCoeffMatrix, hStateX, hFlux'', hCoeffOrig]
      have hReSub (u : Vec 2) :
          matVecMul (matTranspose R) u - e =
            matVecMul (matTranspose R) u -
              matVecMul (matTranspose R) (matVecMul R e) :=
        congrArg (fun z : Vec 2 => matVecMul (matTranspose R) u - z)
          hRe.symm
      calc
        _ = _ := hReSub _
        _ = _ := hLinear _ _
    funext i
    exact congrFun hVector i
  have hDirectionCube := main_directional_raw_ae_to_cube_ae Q hDirection
  have hRotEnergy := main_vectorWeakHaarEnergy_congr_ae Q hDirectionCube
  have hFrameEnergy := main_vectorWeakHaarEnergy_quarterTurnFrame
    (m - 5) F hF
  exact hRotEnergy.trans hFrameEnergy

private theorem main_matrix_eq_of_quadratic_eq_and_symm
    {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hquad : ∀ e : Vec 2,
      dotProduct (star e) (Matrix.mulVec A e) =
        dotProduct (star e) (Matrix.mulVec B e)) :
    A = B := by
  have h0 := hquad (basisVec 0)
  have h1 := hquad (basisVec 1)
  have hsum := hquad (basisVec 0 + basisVec 1)
  have h00 : A 0 0 = B 0 0 := by
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] using h0
  have h11 : A 1 1 = B 1 1 := by
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] using h1
  have hcross : A 0 1 = B 0 1 := by
    have hsum' : A 0 0 + A 0 1 + (A 1 0 + A 1 1) =
        B 0 0 + B 0 1 + (B 1 0 + B 1 1) := by
      simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] using hsum
    rw [hA 1 0, hB 1 0] at hsum'
    linarith
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact hcross
  · calc
      A 1 0 = A 0 1 := hA 1 0
      _ = B 0 1 := hcross
      _ = B 1 0 := hB 0 1
  · exact h11

/-- A samplewise quarter-turn covariance transfers to the expected matrix on
the actual cutoff law. Entrywise integrability is the only analytic premise;
the measure invariance is proved from the whole cutoff-sample law. -/
theorem main_expected_matrix_quarter_turn_relations
    (M : ABKModel 2)
    (N : CutoffSample 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hInt : ∀ i j, Integrable (fun ω => N ω i j)
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hCov : ∀ ω,
      N (rotateCutoffSample quarterTurn
        main_quarterTurn_isSignedPermutation ω) =
        matTranspose quarterTurn * N ω * quarterTurn) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      ∫ ω, N ω i j ∂(Cutoff.cutoffSampleLaw M).toMeasure
    A 0 0 = A 1 1 ∧ A 0 1 = -A 1 0 ∧ A 1 0 = -A 0 1 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let ρ : CutoffSample 2 → CutoffSample 2 :=
    rotateCutoffSample quarterTurn main_quarterTurn_isSignedPermutation
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ∫ ω, N ω i j ∂μ
  have hρMeas : Measurable ρ := by
    exact Cutoff.measurable_rotateCutoffSample quarterTurn
      main_quarterTurn_isSignedPermutation
  have hρMap : Measure.map ρ μ = μ := by
    dsimp [ρ, μ]
    exact Cutoff.map_rotateCutoffSample_cutoffSampleLaw M quarterTurn
      main_quarterTurn_isSignedPermutation
  have hIntegralComp (i j : Fin 2) :
      (∫ ω, N ω i j ∂μ) = ∫ ω, N (ρ ω) i j ∂μ := by
    have hNMap : AEStronglyMeasurable (fun ω => N ω i j) (Measure.map ρ μ) := by
      simpa [hρMap] using (hInt i j).aestronglyMeasurable
    calc
      (∫ ω, N ω i j ∂μ) = ∫ ω, N ω i j ∂(Measure.map ρ μ) := by
        rw [hρMap]
      _ = ∫ ω, N (ρ ω) i j ∂μ :=
        integral_map hρMeas.aemeasurable hNMap
  have hCov00 (ω : CutoffSample 2) : N (ρ ω) 0 0 = N ω 1 1 := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 0) (hCov ω)
    simpa [ρ, quarterTurn, matTranspose, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  have hCov01 (ω : CutoffSample 2) : N (ρ ω) 0 1 = -N ω 1 0 := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 1) (hCov ω)
    simpa [ρ, quarterTurn, matTranspose, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  have hCov10 (ω : CutoffSample 2) : N (ρ ω) 1 0 = -N ω 0 1 := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 1 0) (hCov ω)
    simpa [ρ, quarterTurn, matTranspose, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  refine ⟨?_, ?_, ?_⟩
  · calc
      A 0 0 = ∫ ω, N (ρ ω) 0 0 ∂μ := hIntegralComp 0 0
      _ = ∫ ω, N ω 1 1 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hCov00
      _ = A 1 1 := rfl
  · calc
      A 0 1 = ∫ ω, N (ρ ω) 0 1 ∂μ := hIntegralComp 0 1
      _ = ∫ ω, -N ω 1 0 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hCov01
      _ = -A 1 0 := by rw [integral_neg]
  · calc
      A 1 0 = ∫ ω, N (ρ ω) 1 0 ∂μ := hIntegralComp 1 0
      _ = ∫ ω, -N ω 0 1 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hCov10
      _ = -A 0 1 := by rw [integral_neg]

/-- The actual bottom Gram matrix transforms by conjugation under the actual
quarter-turn of the cutoff sample. -/
theorem main_directional_bottom_pair_covariance_matrix_quarterTurn
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) :
    mainDirectionalBottomPairCovarianceMatrix M m t
        (originCube 2 (m - 5))
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω) =
      matTranspose quarterTurn *
        mainDirectionalBottomPairCovarianceMatrix M m t
          (originCube 2 (m - 5)) ω * quarterTurn := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let R : Mat 2 := quarterTurn
  let N := mainDirectionalBottomPairCovarianceMatrix M m t Q ω
  let NR := mainDirectionalBottomPairCovarianceMatrix M m t Q
    (rotateCutoffSample quarterTurn
      main_quarterTurn_isSignedPermutation ω)
  have hMatrix : NR = matTranspose R * N * R := by
    refine main_matrix_eq_of_quadratic_eq_and_symm
      (A := NR) (B := matTranspose R * N * R) ?_ ?_ ?_
    · intro i j
      exact main_directional_bottom_pair_covariance_matrix_symm M m t Q
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω) i j
    · intro i j
      have hN : ∀ i j, N i j = N j i := by
        intro i j
        exact main_directional_bottom_pair_covariance_matrix_symm
          M m t Q ω i j
      have hNtranspose : Matrix.transpose N = N := by
        ext i j
        exact hN j i
      have hBtranspose : Matrix.transpose (matTranspose R * N * R) =
          matTranspose R * N * R := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, hNtranspose]
        simp [matTranspose, Matrix.mul_assoc]
      have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j)
        hBtranspose
      simpa [Matrix.transpose_apply] using hentry.symm
    · intro e
      have hRe : matVecMul (matTranspose R) (matVecMul R e) = e := by
        simpa [R] using main_quarterTurn_isometry_id e
      have hPrimal := main_old_signed_frame_first_weak_energy_quarterTurn
        M m t ω (0, matVecMul R e)
      have hLoad : quarterTurnLoad (0, matVecMul R e) = (0, e) := by
        rw [main_quarterTurnLoad_components]
        apply Prod.ext
        · ext i
          simp [matVecMul]
        · exact hRe
      have hPrimal' :
          vectorWeakHaarEnergy Q
            (mainDirectionalBottomPrimalDirection M m t Q
              (rotateCutoffSample quarterTurn
                main_quarterTurn_isSignedPermutation ω) e) =
          vectorWeakHaarEnergy Q
            (mainDirectionalBottomPrimalDirection M m t Q ω
              (matVecMul R e)) := by
        change vectorWeakHaarEnergy (originCube 2 (m - 5))
            (fun x i => (oldSignedFrameCanonicalField (originCube 2 (m - 5))
              M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
              (Annealed.sigmaBar M m).2
              (mainInsertionSkewCoefficient m t (originCube 2 (m - 5))
                (rotateCutoffSample quarterTurn
                  main_quarterTurn_isSignedPermutation ω))
              (0, e) x).1 i) =
          vectorWeakHaarEnergy (originCube 2 (m - 5))
            (fun x i => (oldSignedFrameCanonicalField (originCube 2 (m - 5))
              M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
              (Annealed.sigmaBar M m).2
              (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)
              (0, matVecMul R e) x).1 i)
        simpa [hLoad] using hPrimal
      have hReciprocal := main_old_signed_bottom_reciprocal_weak_energy_quarterTurn
        M m t ω (matVecMul R e)
      have hReciprocal' :
          vectorWeakHaarEnergy Q
            (mainDirectionalBottomReciprocalDirection M m t Q
              (rotateCutoffSample quarterTurn
                main_quarterTurn_isSignedPermutation ω) e) =
          vectorWeakHaarEnergy Q
            (mainDirectionalBottomReciprocalDirection M m t Q ω
              (matVecMul R e)) := by
        simpa only [Q, R, hRe] using hReciprocal
      have hSourceRot := main_directional_bottom_pair_covariance_quadratic_eq_source
        M m t Q
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω) e
      have hSource := main_directional_bottom_pair_covariance_quadratic_eq_source
        M m t Q ω (matVecMul R e)
      calc
        dotProduct (star e) (Matrix.mulVec NR e) =
            vectorWeakHaarEnergy Q
              (mainDirectionalBottomPrimalDirection M m t Q
                (rotateCutoffSample quarterTurn
                  main_quarterTurn_isSignedPermutation ω) e) +
              vectorWeakHaarEnergy Q
              (mainDirectionalBottomReciprocalDirection M m t Q
                (rotateCutoffSample quarterTurn
                  main_quarterTurn_isSignedPermutation ω) e) := by
                  simpa [NR] using hSourceRot
        _ = vectorWeakHaarEnergy Q
              (mainDirectionalBottomPrimalDirection M m t Q ω
                (matVecMul R e)) +
              vectorWeakHaarEnergy Q
              (mainDirectionalBottomReciprocalDirection M m t Q ω
                (matVecMul R e)) := by rw [hPrimal', hReciprocal']
        _ = dotProduct (star (matVecMul R e))
          (Matrix.mulVec N (matVecMul R e)) := by
                  simpa [N] using hSource.symm
        _ = dotProduct (star e)
          (Matrix.mulVec (matTranspose R * N * R) e) := by
          have hmul : Matrix.mulVec (matTranspose R * N * R) e =
              Matrix.mulVec (matTranspose R)
                (Matrix.mulVec N (Matrix.mulVec R e)) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
          rw [hmul]
          have htrans :
              dotProduct (star e)
                  (Matrix.mulVec (matTranspose R)
                    (Matrix.mulVec N (Matrix.mulVec R e))) =
                dotProduct (Matrix.mulVec N (Matrix.mulVec R e))
                  (Matrix.mulVec R e) := by
            simpa [matTranspose, star_trivial] using
              (Matrix.dotProduct_transpose_mulVec R e
                (Matrix.mulVec N (Matrix.mulVec R e)))
          calc
            dotProduct (star (Matrix.mulVec R e))
                (Matrix.mulVec N (Matrix.mulVec R e)) =
                dotProduct (Matrix.mulVec N (Matrix.mulVec R e))
                  (Matrix.mulVec R e) := by
                    rw [dotProduct_comm]
                    simp only [star_trivial]
            _ = dotProduct (star e)
                (Matrix.mulVec (matTranspose R)
                  (Matrix.mulVec N (Matrix.mulVec R e))) := htrans.symm
  simpa [NR, N, Q, R] using hMatrix

/-- The actual top physical-flux Gram matrix transforms by conjugation under
the actual quarter-turn of the cutoff sample. -/
theorem main_directional_top_physical_flux_covariance_matrix_quarterTurn
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) :
    mainDirectionalTopPhysicalFluxCovarianceMatrix M m t
        (originCube 2 (m - 5))
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω) =
      matTranspose quarterTurn *
        mainDirectionalTopPhysicalFluxCovarianceMatrix M m t
          (originCube 2 (m - 5)) ω * quarterTurn := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let R : Mat 2 := quarterTurn
  let N := mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω
  let NR := mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q
    (rotateCutoffSample quarterTurn
      main_quarterTurn_isSignedPermutation ω)
  have hMatrix : NR = matTranspose R * N * R := by
    refine main_matrix_eq_of_quadratic_eq_and_symm
      (A := NR) (B := matTranspose R * N * R) ?_ ?_ ?_
    · intro i j
      exact main_directional_top_physical_flux_covariance_matrix_symm
        M m t Q
        (rotateCutoffSample quarterTurn
          main_quarterTurn_isSignedPermutation ω) i j
    · intro i j
      have hN : ∀ i j, N i j = N j i := by
        intro i j
        exact main_directional_top_physical_flux_covariance_matrix_symm
          M m t Q ω i j
      have hNtranspose : Matrix.transpose N = N := by
        ext i j
        exact hN j i
      have hBtranspose : Matrix.transpose (matTranspose R * N * R) =
          matTranspose R * N * R := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, hNtranspose]
        simp [matTranspose, Matrix.mul_assoc]
      have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j)
        hBtranspose
      simpa [Matrix.transpose_apply] using hentry.symm
    · intro e
      have hEnergy :=
        main_directional_top_physical_flux_weak_energy_quarterTurn
          M m t ω e
      have hSourceRot :=
        main_directional_top_physical_flux_covariance_quadratic_eq_source
          M m t Q
          (rotateCutoffSample quarterTurn
            main_quarterTurn_isSignedPermutation ω) e
      have hSource :=
        main_directional_top_physical_flux_covariance_quadratic_eq_source
          M m t Q ω (matVecMul R e)
      calc
        dotProduct (star e) (Matrix.mulVec NR e) =
            vectorWeakHaarEnergy Q
              (mainDirectionalTopPhysicalFluxDirectionError M m t Q
                (rotateCutoffSample quarterTurn
                  main_quarterTurn_isSignedPermutation ω) e) := by
                  simpa [NR] using hSourceRot
        _ = vectorWeakHaarEnergy Q
              (mainDirectionalTopPhysicalFluxDirectionError M m t Q ω
                (matVecMul R e)) := hEnergy
        _ = dotProduct (star (matVecMul R e))
          (Matrix.mulVec N (matVecMul R e)) := by
                  simpa [N] using hSource.symm
        _ = dotProduct (star e)
          (Matrix.mulVec (matTranspose R * N * R) e) := by
          have hmul : Matrix.mulVec (matTranspose R * N * R) e =
              Matrix.mulVec (matTranspose R)
                (Matrix.mulVec N (Matrix.mulVec R e)) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
          rw [hmul]
          have htrans :
              dotProduct (star e)
                  (Matrix.mulVec (matTranspose R)
                    (Matrix.mulVec N (Matrix.mulVec R e))) =
                dotProduct (Matrix.mulVec N (Matrix.mulVec R e))
                  (Matrix.mulVec R e) := by
            simpa [matTranspose, star_trivial] using
              (Matrix.dotProduct_transpose_mulVec R e
                (Matrix.mulVec N (Matrix.mulVec R e)))
          calc
            dotProduct (star (Matrix.mulVec R e))
                (Matrix.mulVec N (Matrix.mulVec R e)) =
                dotProduct (Matrix.mulVec N (Matrix.mulVec R e))
                  (Matrix.mulVec R e) := by
                    rw [dotProduct_comm]
                    simp only [star_trivial]
            _ = dotProduct (star e)
                (Matrix.mulVec (matTranspose R)
                  (Matrix.mulVec N (Matrix.mulVec R e))) := htrans.symm
  simpa [NR, N, Q, R] using hMatrix

end ASDExplicitGamma.Main

end
