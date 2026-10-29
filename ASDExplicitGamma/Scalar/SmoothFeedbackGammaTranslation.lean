/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaTheta
public import ASDExplicitGamma.Scalar.SmoothFeedbackCellTransport
public import ASDExplicitGamma.Native.HeatVHEATSourceHistoryTransport
public import ASDExplicitGamma.Main.DirectionalSymmetry

/-! Stationarity of the actual directional Gamma across translated cells. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Variational ASDExplicitGamma.Triadic
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main
open Algsuperdiff.Section3

noncomputable section

private theorem gamma_translate_ellipticity
    {U : Set (Vec 2)} {a : CoeffField 2} {lam Lam : ℝ} (z : Vec 2)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn lam Lam (translateSet z U) (translateCoeffField (-z) a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hshift : Measurable (fun x : Vec 2 => x - z) :=
      (continuous_id.sub continuous_const).measurable
    have hcomp : Measurable (fun x i j =>
        if x - z ∈ U then a (x - z) i j else 0) := hEll.1.comp hshift
    have hEq : (fun x i j => if x - z ∈ U then a (x - z) i j else 0) =
        (fun x i j => if x ∈ translateSet z U then
          translateCoeffField (-z) a x i j else 0) := by
      funext x i j
      by_cases hx : x - z ∈ U
      · have hxt : x ∈ translateSet z U := by
          rw [mem_translateSet_iff_sub_mem]
          simpa [sub_eq_add_neg, add_assoc] using hx
        have hsub : x - z = (fun i => x i + -z i) := by
          ext i
          simp only [Pi.sub_apply]
          ring
        have hxsub : (fun i => x i + -z i) ∈ U := by
          simpa only [hsub] using hx
        simp [hsub, hxsub, hxt, translateCoeffField]
      · have hxt : x ∉ translateSet z U := by
          intro h
          rw [mem_translateSet_iff_sub_mem] at h
          exact hx (by simpa [sub_eq_add_neg, add_assoc] using h)
        have hsub : x - z = (fun i => x i + -z i) := by
          ext i
          simp only [Pi.sub_apply]
          ring
        have hxsub : (fun i => x i + -z i) ∉ U := by
          simpa only [hsub] using hx
        simp [hsub, hxsub, hxt]
    simpa [hEq] using hcomp
  · intro x hx
    have hx' : x - z ∈ U := by
      rw [mem_translateSet_iff_sub_mem] at hx
      exact hx
    have hsub : x - z = (fun i => x i + -z i) := by
      ext i
      simp only [Pi.sub_apply]
      ring
    simpa [translateCoeffField, hsub] using hEll.2 (x - z) hx'

private theorem gamma_scalarCellResponseTest_energy_eq_Mu
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    blockEnergyAverage (openCubeSet Q) a
        (scalarCellResponseTest Q a hEll P) = Mu (openCubeSet Q) P a := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let _ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hU.isFiniteMeasure_restrict_volume
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  let Msys := scalarCellSystem Q a hEll
  have hmu : ∀ T : BlockVec 2,
      Mu (openCubeSet Q) T a = Msys.toMuHilbertRealization.muCandidate T := by
    intro T
    exact (lemmaV_canonical_muCandidate_eq_Mu hU hEll
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) T).symm
  have h := R.recoveredField_blockEnergyAverage_eq_mu Msys hmu P
  simpa [R, Msys, scalarCellSystem, scalarCellResponseTest] using h

private theorem gamma_scalarCellResponseTest_admissible
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    IsBlockMuAdmissible (openCubeSet Q) P (scalarCellResponseTest Q a hEll P) := by
  have h := scalar_cell_response_test_variation Q a hEll P
  refine ⟨memVectorL2_fst_of_memBlockL2 h.1, ?_,
    memVectorL2_snd_of_memBlockL2 h.1, ?_⟩
  · simpa [BlockState.eval] using h.2.1
  · simpa [BlockState.eval] using h.2.2

/-- Pulling a cell response to an origin cube preserves the recovered field
after the actual spatial translation. -/
private theorem scalarCellResponseTest_translate_origin
    (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam
      (openCubeSet (originCube 2 Q.scale)) a)
    (P : BlockVec 2) :
    let O := originCube 2 Q.scale
    let z := triadicCubeShift Q
    let aQ := translateCoeffField (-z) a
    let hEllQ : IsEllipticFieldOn lam Lam (openCubeSet Q) aQ := by
      have hOQ : openCubeSet Q = translateSet z (openCubeSet O) := by
        simpa [z, O] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
      have h := gamma_translate_ellipticity z hEll
      rw [← hOQ] at h
      exact h
    (scalarCellResponseTest Q aQ hEllQ P).eval =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => (scalarCellResponseTest O a hEll P).eval (x - z)) := by
  classical
  dsimp only
  let O : TriadicCube 2 := originCube 2 Q.scale
  let z : Vec 2 := triadicCubeShift Q
  let aQ : CoeffField 2 := translateCoeffField (-z) a
  let X := scalarCellResponseTest O a hEll P
  let Y := X.translate z
  have hOQ : openCubeSet Q = translateSet z (openCubeSet O) := by
    simpa [z, O] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let hEllQ : IsEllipticFieldOn lam Lam (openCubeSet Q) aQ := by
    simpa [hOQ, aQ] using gamma_translate_ellipticity z hEll
  have hY : Y.eval = fun x => X.eval (x - z) := by
    funext x
    rfl
  have hXadm : IsBlockMuAdmissible (openCubeSet O) P X := by
    exact gamma_scalarCellResponseTest_admissible O a hEll P
  have hYadm : IsBlockMuAdmissible (openCubeSet Q) P Y := by
    have h := isBlockMuAdmissible_translateSet
      (U := openCubeSet O) hXadm z
    simpa [hOQ, Y, BlockState.translate] using h
  have hCoeff : translateCoeffField z aQ = a := by
    ext x i j
    simp [aQ, translateCoeffField, add_assoc]
  have hEnergy : blockEnergyAverage (openCubeSet Q) aQ Y =
      blockEnergyAverage (openCubeSet O) a X := by
    rw [hOQ]
    simpa [blockEnergyAverage, Y, hCoeff] using
      (volumeAverage_blockEnergyDensity_translate_forward z
        (openCubeSet O) aQ X)
  have hMu : Mu (openCubeSet Q) P aQ = Mu (openCubeSet O) P a := by
    calc
      Mu (openCubeSet Q) P aQ = Mu (translateSet z (openCubeSet O)) P aQ := by
        rw [hOQ]
      _ = Mu (openCubeSet O) P (translateCoeffField z aQ) :=
        Mu_translateSet_eq_translateCoeffField z (openCubeSet O) P aQ
      _ = Mu (openCubeSet O) P a := by rw [hCoeff]
  have hYenergy : blockEnergyAverage (openCubeSet Q) aQ Y =
      Mu (openCubeSet Q) P aQ := by
    calc
      _ = blockEnergyAverage (openCubeSet O) a X := hEnergy
      _ = Mu (openCubeSet O) P a :=
        gamma_scalarCellResponseTest_energy_eq_Mu O a hEll P
      _ = Mu (openCubeSet Q) P aQ := hMu.symm
  let hUQ := isOpenBoundedConvexDomain_openCubeSet Q
  let _ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hUQ.isFiniteMeasure_restrict_volume
  let R := (lemmaVRecoveryData hUQ).toMuCorrectionSpaceRecoveryData
  let Msys := scalarCellSystem Q aQ hEllQ
  have hmuQ : Mu (openCubeSet Q) P aQ =
      Msys.toMuHilbertRealization.muCandidate P := by
    exact (lemmaV_canonical_muCandidate_eq_Mu hUQ hEllQ
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) P).symm
  have hminY : toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval =
      Msys.toMuHilbertRealization.minimizerMap P := by
    apply Msys.toMuHilbertRealization.eq_minimizerMap_of_quadraticEnergy_le_muCandidate
      P (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval) ?_ ?_
    · exact hYadm.toCorrectionFieldData_mem_correctionSpace
    · change quadraticEnergy (energyBilinOfOperator
        Msys.toMuOperatorRealization.operator)
        (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval) ≤
          Msys.toMuHilbertRealization.muCandidate P
      rw [Msys.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        (X := Y) hYadm.memBlockL2_eval]
      rw [hYenergy, hmuQ]
  have hminTest : toHilbertBlockL2OfBlockField
      (scalar_cell_response_test_memL2 Q aQ hEllQ P) =
      Msys.toMuHilbertRealization.minimizerMap P :=
    R.recoveredField_minimizer_eq Msys P
  have hHilbert := hminY.trans hminTest.symm
  have hYae : hilbertBlockL2ToBlockL2
      (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval) =ᵐ[
        volumeMeasureOn (openCubeSet Q)] fun x => Y.eval x := by
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval,
      coeFn_hilbertBlockL2ToBlockL2
        (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval)] with x hx hy
    rw [hy, hx]
    simp [hilbertifyBlockField]
  have hTestRec := lemmaV_recovered_minimizer_ae hUQ hEllQ
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) P
  have hTestAe : hilbertBlockL2ToBlockL2
      (toHilbertBlockL2OfBlockField (scalar_cell_response_test_memL2 Q aQ hEllQ P)) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      fun x => (scalarCellResponseTest Q aQ hEllQ P).eval x := by
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField
        (scalar_cell_response_test_memL2 Q aQ hEllQ P),
      coeFn_hilbertBlockL2ToBlockL2
        (toHilbertBlockL2OfBlockField
          (scalar_cell_response_test_memL2 Q aQ hEllQ P))] with x hx hy
    rw [hy, hx]
    simp [hilbertifyBlockField]
  have hEq := congrArg hilbertBlockL2ToBlockL2 hHilbert
  filter_upwards [hYae, hTestAe] with x hy ht
  have hx := congrArg (fun F : BlockL2 (openCubeSet Q) => F x) hEq
  rw [hy, ht] at hx
  exact hx.symm

private theorem gamma_actual_coeff_translate
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    let O := originCube 2 Q.scale
    let z := triadicCubeShift Q
    let ω0 := Cutoff.translateCutoffSample z ω
    let aQ := responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)
    let a0 := responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m O ω0)
    ∀ x ∈ openCubeSet Q, aQ x = translateCoeffField (-z) a0 x := by
  intro O z ω0 aQ a0 x hx
  have hOQ : openCubeSet Q = translateSet z (openCubeSet O) := by
    simpa [z, O] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hxO : x - z ∈ openCubeSet O := by
    rw [hOQ, mem_translateSet_iff_sub_mem] at hx
    exact hx
  change responsePlanarCoefficient (M.nu / (Annealed.sigmaBar M m : ℝ))
      (responseCoefficientExtension (oldCutoffSkewCoefficient m Q ω) x /
        (Annealed.sigmaBar M m : ℝ)) =
    responsePlanarCoefficient (M.nu / (Annealed.sigmaBar M m : ℝ))
      (responseCoefficientExtension
        (oldCutoffSkewCoefficient m O ω0) (x - z) /
        (Annealed.sigmaBar M m : ℝ))
  rw [old_cutoff_skew_coefficient_value m Q ω hx,
    old_cutoff_skew_coefficient_value m O ω0 hxO,
    Cutoff.cutoff_translateCutoffSample]
  simp [z, sub_eq_add_neg, add_assoc]

/-- The directional affine Gamma on a physical cell is its centered-origin
counterpart evaluated at the translated cutoff sample. -/
theorem smooth_feedback_cell_directional_gamma_translate_origin
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellDirectionalGamma M m Q e ω =
      smoothFeedbackCellDirectionalGamma M m (originCube 2 Q.scale) e
        (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
  classical
  let O : TriadicCube 2 := originCube 2 Q.scale
  let z : Vec 2 := triadicCubeShift Q
  let ω0 : Cutoff.CutoffSample 2 := Cutoff.translateCutoffSample z ω
  let aQ : CoeffField 2 := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)
  let a0 : CoeffField 2 := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m O ω0)
  let aT : CoeffField 2 := translateCoeffField (-z) a0
  let hEllQ := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
  let hEll0 := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet O) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m O ω0)
  let hEllT := gamma_translate_ellipticity z hEll0
  have hOQ : openCubeSet Q = translateSet z (openCubeSet O) := by
    simpa [z, O] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEllTQ := by
    have h := hEllT
    rw [← hOQ] at h
    exact h
  have hCoeff : ∀ x ∈ openCubeSet Q, aQ x = aT x := by
    exact gamma_actual_coeff_translate M m Q ω
  have hCoeffAe : aQ =ᵐ[volumeMeasureOn (openCubeSet Q)] aT := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact hCoeff x hx
  have hTestCong :
      (scalarCellResponseTest Q aQ hEllQ (e, 0)).eval =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q aT hEllTQ (e, 0)).eval := by
    exact Main.main_scalarCellResponseTest_congr_coeff_ae
      Q aQ aT hEllQ hEllTQ hCoeffAe (e, 0)
  have hTestTranslate := scalarCellResponseTest_translate_origin
    Q a0 hEll0 (e, 0)
  have hTest :
      (scalarCellResponseTest Q aQ hEllQ (e, 0)).eval =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (fun x => (scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z)) := by
    exact hTestCong.trans hTestTranslate
  have hTop :
      (fun x => ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x).1 - e) =ᵐ[
        volumeMeasureOn (openCubeSet Q)] fun x =>
      ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z)).1 - e := by
    filter_upwards [hTest] with x hx
    exact congrArg (fun V : BlockVec 2 => V.1 - e) hx
  have hFlux : (fun x => (blockMatVecMul (blockCoeffField aQ x)
        ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x)).2) =ᵐ[
          volumeMeasureOn (openCubeSet Q)] fun x =>
      (blockMatVecMul (blockCoeffField a0 (x - z))
        ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z))).2 := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q), hTest] with x hx hX
    have hC := hCoeff x hx
    have hBlockCoeff : blockCoeffField aQ x = blockCoeffField aT x := by
      simp [blockCoeffField, hC]
    change (blockMatVecMul (blockCoeffField aQ x)
        ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x)).2 = _
    calc
      _ = (blockMatVecMul (blockCoeffField aT x)
          ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z))).2 := by
            rw [hX, hBlockCoeff]
      _ = (blockMatVecMul (blockCoeffField a0 (x - z))
          ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z))).2 := by
            change (blockMatVecMul
              (blockMatrixOfCoeff (a0 (x + -z)))
              ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z))).2 =
              (blockMatVecMul
                (blockMatrixOfCoeff (a0 (x - z)))
                ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z))).2
            have hArg : x + -z = x - z := by
              ext i
              simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
              ring
            rw [hArg]
  have hTopEnergy := smooth_feedback_vector_weak_energy_congr_ae Q hTop
  have hFluxEnergy := smooth_feedback_vector_weak_energy_congr_ae Q hFlux
  have hTopEnergy' :
      vectorWeakHaarEnergy Q (fun x i =>
        ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x).1 i - e i) =
      vectorWeakHaarEnergy Q (fun x i =>
        ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z)).1 i - e i) := by
    calc
      _ = vectorWeakHaarEnergy Q
          (fun x => ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x).1 - e) := by
            congr 1
      _ = vectorWeakHaarEnergy Q
          (fun x => ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z)).1 - e) :=
            hTopEnergy
      _ = _ := by
            congr 1
  have hFluxEnergy' :
      vectorWeakHaarEnergy Q (fun x i =>
        (blockMatVecMul (blockCoeffField aQ x)
          ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x)).2 i) =
      vectorWeakHaarEnergy Q (fun x i =>
        (blockMatVecMul (blockCoeffField a0 (x - z))
          ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z))).2 i) := by
    simpa using hFluxEnergy
  have hz : smoothFeedbackCubeTranslationVector O Q.index = z := by
    change (fun i => (Q.index i : ℝ) * cubeScaleFactor (originCube 2 Q.scale)) =
      (fun i => (Q.index i : ℝ) * cubeScaleFactor Q)
    funext i
    simp [cubeScaleFactor, originCube]
  have hQcube : translateCube Q.index O = Q := by
    cases Q
    simp [O, translateCube, originCube]
  have hTopTranslate' := vectorWeakHaarEnergy_translateCube O Q.index
    (fun x i => ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval x).1 i - e i)
  have hFluxTranslate' := vectorWeakHaarEnergy_translateCube O Q.index
    (fun x i => (blockMatVecMul (blockCoeffField a0 x)
      ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval x)).2 i)
  rw [hQcube, hz] at hTopTranslate' hFluxTranslate'
  have hTopDefectQ : smoothFeedbackCellAffineTopDefect M m Q e ω =
      (fun x i => ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x).1 i - e i) := by
    funext x i
    simp [smoothFeedbackCellAffineTopDefect,
      smoothFeedbackCellAffineResidual, aQ]
  have hFluxFieldQ : smoothFeedbackCellAffineReciprocalGradient M m Q e ω =
      (fun x i =>
        (blockMatVecMul (blockCoeffField aQ x)
          ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x)).2 i) := by
    funext x i
    simp [smoothFeedbackCellAffineReciprocalGradient, scalarCoefficientFlux,
      smoothFeedbackCellAffineResidual, aQ]
  have hGammaQ : smoothFeedbackCellDirectionalGamma M m Q e ω =
      vectorWeakHaarEnergy Q
          (fun x i => ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x).1 i - e i) +
        vectorWeakHaarEnergy Q (fun x i =>
          (blockMatVecMul (blockCoeffField aQ x)
            ((scalarCellResponseTest Q aQ hEllQ (e, 0)).eval x)).2 i) := by
    unfold smoothFeedbackCellDirectionalGamma
    rw [hTopDefectQ, hFluxFieldQ]
  have hTopDefect0 : smoothFeedbackCellAffineTopDefect M m O e ω0 =
      (fun x i => ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval x).1 i - e i) := by
    funext x i
    simp [smoothFeedbackCellAffineTopDefect,
      smoothFeedbackCellAffineResidual, a0]
  have hFluxField0 : smoothFeedbackCellAffineReciprocalGradient M m O e ω0 =
      (fun x i =>
        (blockMatVecMul (blockCoeffField a0 x)
          ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval x)).2 i) := by
    funext x i
    simp [smoothFeedbackCellAffineReciprocalGradient, scalarCoefficientFlux,
      smoothFeedbackCellAffineResidual, a0]
  have hGamma0 : smoothFeedbackCellDirectionalGamma M m O e ω0 =
      vectorWeakHaarEnergy O
          (fun x i => ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval x).1 i - e i) +
        vectorWeakHaarEnergy O (fun x i =>
          (blockMatVecMul (blockCoeffField a0 x)
            ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval x)).2 i) := by
    unfold smoothFeedbackCellDirectionalGamma
    rw [hTopDefect0, hFluxField0]
  rw [hGammaQ, hGamma0]
  calc
    _ = vectorWeakHaarEnergy Q (fun x i =>
          ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z)).1 i - e i) +
        vectorWeakHaarEnergy Q (fun x i =>
          (blockMatVecMul (blockCoeffField a0 (x - z))
            ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval (x - z))).2 i) := by
      rw [hTopEnergy', hFluxEnergy']
    _ = vectorWeakHaarEnergy O (fun x i =>
          ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval x).1 i - e i) +
        vectorWeakHaarEnergy O (fun x i =>
          (blockMatVecMul (blockCoeffField a0 x)
            ((scalarCellResponseTest O a0 hEll0 (e, 0)).eval x)).2 i) := by
      rw [hTopTranslate', hFluxTranslate']

end

end ASDExplicitGamma.Scalar

end
