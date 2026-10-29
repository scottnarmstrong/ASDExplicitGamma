module

public import ASDExplicitGamma.Scalar.SmoothFeedbackResponseSpace
public import ASDExplicitGamma.Scalar.SmoothFeedbackTopPatchIdentity
public import ASDExplicitGamma.Scalar.SmoothFeedbackTopParentComplementaryPatch
public import ASDExplicitGamma.Native.OldSignedCellProjection
public import ASDExplicitGamma.Native.OldSignedLocalData
public import ASDExplicitGamma.Variational.CompatibleCoercivity
public import ASDExplicitGamma.Variational.ForcedSourceFeedback
public import ASDExplicitGamma.Variational.PairedBessel

/-! Paired Bessel estimates for the actual parent-top minus reflected
descendant-bottom fields. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3

noncomputable section

private theorem responseSpace_coeff_ae
    {U : Set (Vec 2)} {a b : CoeffField 2} {X : BlockState 2}
    (hCoeff : a =ᵐ[volumeMeasureOn U] b)
    (hX : BlockResponseSpace a U X) : BlockResponseSpace b U X := by
  refine ⟨hX.1, hX.2.1, ?_⟩
  intro Y hY
  have hIntegrand : (fun x => blockVecDot (Y.eval x)
      (blockMatVecMul (blockCoeffField b x) (X.eval x))) =ᵐ[
        volumeMeasureOn U]
      (fun x => blockVecDot (Y.eval x)
        (blockMatVecMul (blockCoeffField a x) (X.eval x))) := by
    filter_upwards [hCoeff] with x hx
    change blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (b x)) (X.eval x)) =
      blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (a x)) (X.eval x))
    rw [← hx]
  rw [integral_congr_ae hIntegrand]
  exact hX.2.2 Y hY

private theorem complementary_paired_bessel_of_responses
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (S T : BlockState 2)
    (hS : BlockResponseSpace a (openCubeSet Q) S)
    (hSmem : MemBlockL2 (openCubeSet Q) S.eval)
    (hT : BlockResponseSpace a (openCubeSet R) T)
    (hTmem : MemBlockL2 (openCubeSet R) T.eval) :
    let Z := (S + (-1 : ℝ) • pairedReflectState a T)
    vecDot (pairedPotentialMean (openCubeSet R) Z)
        (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight⁻¹
          (pairedPotentialMean (openCubeSet R) Z)) +
      vecDot (pairedFluxImageMean (openCubeSet R) a Z)
        (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight⁻¹
          (pairedFluxImageMean (openCubeSet R) a Z)) ≤
      blockPairingAverage (openCubeSet R) a Z Z ∧
      vecDot (pairedFluxImageMean (openCubeSet R) a Z)
        (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight⁻¹
          (pairedFluxImageMean (openCubeSet R) a Z)) ≤
        blockPairingAverage (openCubeSet R) a Z Z := by
  dsimp only
  let UQ := openCubeSet Q
  let UR := openCubeSet R
  let hEllR := hEll.mono (measurableSet_openCubeSet R) hRQ
  let : Fact (volume UQ < ⊤) := ⟨volume_openCubeSet_lt_top Q⟩
  let : IsFiniteMeasure (volumeMeasureOn UQ) := by infer_instance
  let : Fact (volume UR < ⊤) := ⟨volume_openCubeSet_lt_top R⟩
  let : IsFiniteMeasure (volumeMeasureOn UR) := by infer_instance
  let S_R := S
  let J := pairedReflectState a T
  let Z := S_R + (-1 : ℝ) • J
  have hS_R : BlockResponseSpace a UR S_R :=
    blockResponseSpace_restrict_subcube Q R hRQ a hEll S hS hSmem
  have hS_Rmem : MemBlockL2 UR S_R.eval :=
    hSmem.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hJ : BlockResponseSpace a UR J :=
    pairedReflectState_mem_responseSpace'
      (isOpenBoundedConvexDomain_openCubeSet R) hEllR hT
      (by simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hTmem)
  have hJmem : MemBlockL2 UR J.eval :=
    compatibleReflectState_memBlockL2 hEllR T hTmem
  have hZ : BlockResponseSpace a UR Z := by
    simpa [Z, J, S_R] using
      blockResponseSpace_sub hEllR S_R J hS_R hJ hS_Rmem hJmem
  have hZmem : MemBlockL2 UR Z.eval := by
    change MemBlockL2 UR (S_R.eval + (-1 : ℝ) • J.eval)
    exact hS_Rmem.add (hJmem.const_smul (-1))
  have hBessel := pairedBessel_openCubeSet hEllR Z hZ hZmem
  have hvol : 0 < (volume UR).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos R
  obtain ⟨_, hCoarse, _, _, _, _, hDpositive, _⟩ :=
    exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet R)
      hEllR hvol
  have hD : (coarseBlockMatrix UR a).lowerRight.PosDef := by
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpositive
  have hPotentialNonneg : 0 ≤
      vecDot (pairedPotentialMean UR Z)
        (matVecMul (coarseBlockMatrix UR a).lowerRight⁻¹
          (pairedPotentialMean UR Z)) := by
    have h := hD.inv.posSemidef.dotProduct_mulVec_nonneg
      (pairedPotentialMean UR Z)
    simpa only [star_trivial, vecDot, matVecMul, Matrix.mulVec, dotProduct] using h
  have hFluxTerm :
      vecDot (pairedFluxImageMean UR a Z)
        (matVecMul (coarseBlockMatrix UR a).lowerRight⁻¹
          (pairedFluxImageMean UR a Z)) ≤ blockPairingAverage UR a Z Z := by
    dsimp only [Z, J, S_R] at hBessel hPotentialNonneg ⊢
    linarith
  exact ⟨by simpa [UQ, UR, Z, J, S_R] using hBessel,
    by simpa [UQ, UR, Z, J, S_R] using hFluxTerm⟩

private theorem scalar_variation_first_average_zero
    (Q : TriadicCube 2) (X : BlockState 2) (P : BlockVec 2)
    (hVar : ScalarVariation (openCubeSet Q) (fun x => X.eval x - P))
    (hP : P.1 = 0) :
    volumeAverageVec (openCubeSet Q) X.potential = 0 := by
  have hPotential : IsPotentialZeroTraceOn (openCubeSet Q) X.potential := by
    simpa [BlockState.eval, hP] using hVar.2.1
  have hIntegral := IsPotentialZeroTraceOn.integral_eq_zero hPotential
  funext i
  apply volumeAverage_eq_zero_of_integral_eq_zero
  exact congrFun hIntegral i

private theorem complementary_flux_mean
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (S T : BlockState 2)
    (hSmem : MemBlockL2 (openCubeSet Q) S.eval)
    (hTmem : MemBlockL2 (openCubeSet R) T.eval)
    (hTmean : volumeAverageVec (openCubeSet R) T.potential = 0) :
    let Z := (S + (-1 : ℝ) • pairedReflectState a T)
    pairedFluxImageMean (openCubeSet R) a Z =
      volumeAverageVec (openCubeSet R) (fun x =>
        (blockMatVecMul (blockCoeffField a x) (S.eval x)).2) := by
  dsimp only
  let UQ := openCubeSet Q
  let UR := openCubeSet R
  let hEllR := hEll.mono (measurableSet_openCubeSet R) hRQ
  let : Fact (volume UQ < ⊤) := ⟨volume_openCubeSet_lt_top Q⟩
  let : IsFiniteMeasure (volumeMeasureOn UQ) := by infer_instance
  let : Fact (volume UR < ⊤) := ⟨volume_openCubeSet_lt_top R⟩
  let : IsFiniteMeasure (volumeMeasureOn UR) := by infer_instance
  let S_R := S
  let J := pairedReflectState a T
  let Z := S_R + (-1 : ℝ) • J
  have hSmemR : MemBlockL2 UR S_R.eval :=
    hSmem.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hASmem : MemBlockL2 UR (scalarCoefficientFlux a S_R.eval) :=
    scalar_coefficient_flux_memL2 R a hEllR hSmemR
  have hLowerMem : MemVectorL2 UR (fun x =>
      (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2) := by
    simpa [scalarCoefficientFlux] using
      memVectorL2_snd_of_memBlockL2 hASmem
  have hTpotMem : MemVectorL2 UR T.potential :=
    memVectorL2_fst_of_memBlockL2 hTmem
  have hLowerInt (i : Fin 2) : IntegrableOn
      (fun x => (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2 i) UR :=
    CorrectionFieldData.integrableOn_coord_of_memVectorL2 hLowerMem i
  have hTpotInt (i : Fin 2) : IntegrableOn (fun x => T.potential x i) UR :=
    CorrectionFieldData.integrableOn_coord_of_memVectorL2 hTpotMem i
  have hPoint (x : Vec 2) (hx : x ∈ UR) :
      (blockMatVecMul (blockCoeffField a x) (Z.eval x)).2 =
        (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2 - T.potential x := by
    change (blockMatVecMul (blockCoeffField a x)
        (S_R.eval x + (-1 : ℝ) • J.eval x)).2 = _
    rw [blockMatVecMul_add, blockMatVecMul_smul,
      pairedReflectState_action hEllR T hx]
    ext i
    simp [BlockState.eval, sub_eq_add_neg]
  have hAE : (fun x =>
      (blockMatVecMul (blockCoeffField a x) (Z.eval x)).2) =ᵐ[
        volumeMeasureOn UR] (fun x =>
          (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2 - T.potential x) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hPoint x hx
  have hSubAverage : volumeAverageVec UR (fun x =>
      (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2 - T.potential x) =
      volumeAverageVec UR (fun x =>
        (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2) -
          volumeAverageVec UR T.potential := by
    funext i
    change volumeAverage UR (fun x =>
        (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2 i -
          T.potential x i) = _
    exact volumeAverage_sub (hLowerInt i) (hTpotInt i)
  calc
    pairedFluxImageMean UR a Z = volumeAverageVec UR
        (fun x => (blockMatVecMul (blockCoeffField a x) (Z.eval x)).2) := rfl
    _ = volumeAverageVec UR (fun x =>
          (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2 - T.potential x) :=
        forcedSource_volumeAverageVec_congr_ae hAE
    _ = volumeAverageVec UR (fun x =>
          (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2) -
            volumeAverageVec UR T.potential := hSubAverage
    _ = volumeAverageVec UR (fun x =>
          (blockMatVecMul (blockCoeffField a x) (S_R.eval x)).2) := by
        rw [hTmean]
        simp

/-- On every descendant, the actual parent top-affine response minus the
coefficient reflection of the actual local bottom-affine response is a
finite-energy compatible field, so paired Bessel applies with that cell's
true lower-right response block. Its paired flux-image mean is exactly the
descendant average of the source reciprocal-gradient observable, and its
inverse-block quadratic is bounded by the complementary energy. -/
theorem smooth_feedback_descendant_top_complementary_paired_bessel
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2)
    (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) :
    let k := oldCutoffSkewCoefficient m Q ω
    let σ := (Annealed.sigmaBar M m : ℝ)
    let a := responseFramePlanarCoefficientField M.nu σ k
    let Ptop : BlockVec 2 := (e, 0)
    let Pbot : BlockVec 2 := (0, e)
    let hEll := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property k
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let S := scalarCellResponseTest Q a hEll Ptop
    let F : Vec 2 → BlockVec 2 := fun _ => Pbot
    let hF : MemBlockL2 (openCubeSet Q) F := memLp_const Pbot
    let T := oldSignedCellResidual Q R hRQ M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k F hF
    let Tstate : BlockState 2 := ⟨fun x => (T x).1, fun x => (T x).2⟩
    let Z := S + (-1 : ℝ) • pairedReflectState a Tstate
    (vecDot (pairedPotentialMean (openCubeSet R) Z)
        (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight⁻¹
          (pairedPotentialMean (openCubeSet R) Z)) +
      vecDot (pairedFluxImageMean (openCubeSet R) a Z)
        (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight⁻¹
          (pairedFluxImageMean (openCubeSet R) a Z)) ≤
      blockPairingAverage (openCubeSet R) a Z Z) ∧
      vecDot (pairedFluxImageMean (openCubeSet R) a Z)
        (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight⁻¹
          (pairedFluxImageMean (openCubeSet R) a Z)) ≤
        blockPairingAverage (openCubeSet R) a Z Z ∧
      pairedFluxImageMean (openCubeSet R) a Z =
        volumeAverageVec (openCubeSet R)
          (smoothFeedbackCellAffineReciprocalGradient M m Q e ω) := by
  classical
  dsimp only
  let k := oldCutoffSkewCoefficient m Q ω
  let σ := (Annealed.sigmaBar M m : ℝ)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let Ptop : BlockVec 2 := (e, 0)
  let Pbot : BlockVec 2 := (0, e)
  let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
  let kR := oldSignedCellCoefficient Q R hRQ k
  let aR := responseFramePlanarCoefficientField M.nu σ kR
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k
  let hEllR := hEll.mono (measurableSet_openCubeSet R) hRQ
  let S := scalarCellResponseTest Q a hEll Ptop
  let F : Vec 2 → BlockVec 2 := fun _ => Pbot
  let hF : MemBlockL2 (openCubeSet Q) F := memLp_const Pbot
  let T := oldSignedCellResidual Q R hRQ M.nu σ M.nu_pos
    (Annealed.sigmaBar M m).property k F hF
  let Tstate : BlockState 2 := ⟨fun x => (T x).1, fun x => (T x).2⟩
  have hEllLocal := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet R) M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property kR
  have hFR : MemBlockL2 (openCubeSet R) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hFRconst : toHilbertBlockL2OfBlockField hFR =
      (scalarFrameRealization R M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property kR).constantField Pbot := by
    have hconst : toHilbertBlockL2OfBlockField hFR =
        blockVecToHilbertBlockL2Const Pbot := by
      apply Lp.ext
      filter_upwards [coeFn_toHilbertBlockL2OfBlockField hFR,
        coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet R) Pbot] with x hx hy
      simpa [F] using hx.trans hy.symm
    exact hconst.trans (by rfl)
  have hTeq : (fun x => (T x : BlockVec 2)) = scalarResidualField R M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property kR
      ((scalarFrameRealization R M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property kR).constantField Pbot) := by
    funext x
    change scalarResidualField R M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property kR
      (toHilbertBlockL2OfBlockField hFR) x = _
    rw [hFRconst]
  have hT : BlockResponseSpace aR (openCubeSet R) Tstate := by
    have hResidual := scalarFrameResidual_mem_responseSpace R M.nu σ
      M.nu_pos (Annealed.sigmaBar M m).property kR Pbot
    simpa [Tstate, hTeq, BlockState.eval] using hResidual
  have hTmem : MemBlockL2 (openCubeSet R) Tstate.eval := by
    change MemBlockL2 (openCubeSet R) T
    exact T.property
  have hCoeff : aR =ᵐ[volumeMeasureOn (openCubeSet R)] a := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    simp only [aR, a, responseFramePlanarCoefficientField]
    rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
  have hTparent : BlockResponseSpace a (openCubeSet R) Tstate :=
    responseSpace_coeff_ae hCoeff hT
  have hS : BlockResponseSpace a (openCubeSet Q) S :=
    scalarCellResponseTest_mem_responseSpace Q a hEll Ptop
  have hSmem : MemBlockL2 (openCubeSet Q) S.eval :=
    scalar_cell_response_test_memL2 Q a hEll Ptop
  have hTResidualAE := scalarFrameResidual_eq_responseTest_ae R M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property kR Pbot
  have hTestVar := scalar_cell_response_test_variation R aR hEllLocal Pbot
  have hTtest : Tstate.eval =ᵐ[volumeMeasureOn (openCubeSet R)]
      (scalarCellResponseTest R aR hEllLocal Pbot).eval := by
    filter_upwards [hTResidualAE] with x hx
    calc
      Tstate.eval x = (T x : BlockVec 2) := by rfl
      _ = scalarResidualField R M.nu σ M.nu_pos
          (Annealed.sigmaBar M m).property kR
          ((scalarFrameRealization R M.nu σ M.nu_pos
            (Annealed.sigmaBar M m).property kR).constantField Pbot) x :=
              congrFun hTeq x
      _ = (scalarCellResponseTest R aR hEllLocal Pbot).eval x := hx
  have hTvarAE : (fun x => (scalarCellResponseTest R aR hEllLocal Pbot).eval x - Pbot) =ᵐ[
      volumeMeasureOn (openCubeSet R)]
      (fun x => Tstate.eval x - Pbot) :=
    hTtest.symm.mono fun x hx =>
      congrArg (fun z : BlockVec 2 => z - Pbot) hx
  have hTvar := old_signed_scalar_variation_congr_ae hTvarAE hTestVar
  have hTmean := scalar_variation_first_average_zero R Tstate Pbot hTvar
    (by simp [Pbot])
  have hBessel := complementary_paired_bessel_of_responses
    Q R hRQ a hEll S Tstate hS hSmem hTparent hTmem
  have hFluxMean := complementary_flux_mean Q R hRQ a hEll S Tstate
    hSmem hTmem hTmean
  have hSResidualAE := scalarFrameResidual_eq_responseTest_ae Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k Ptop
  have hSProjectionAE := smooth_feedback_affine_projection_ae M m Q e ω
  have hSActual : S.eval =ᵐ[volumeMeasureOn (openCubeSet Q)]
      smoothFeedbackCellAffineResidual M m Q e ω := by
    filter_upwards [hSResidualAE, hSProjectionAE] with x hResidual hProjection
    exact hResidual.symm.trans hProjection
  have hSActualR : S.eval =ᵐ[volumeMeasureOn (openCubeSet R)]
      smoothFeedbackCellAffineResidual M m Q e ω :=
    ae_restrict_of_ae_restrict_of_subset hRQ hSActual
  have hGammaAE : (fun x =>
      (blockMatVecMul (blockCoeffField a x) (S.eval x)).2) =ᵐ[
        volumeMeasureOn (openCubeSet R)]
      smoothFeedbackCellAffineReciprocalGradient M m Q e ω := by
    filter_upwards [hSActualR] with x hx
    rw [hx]
    rfl
  have hGammaMean := forcedSource_volumeAverageVec_congr_ae hGammaAE
  refine ⟨?_, ?_, ?_⟩
  · simpa [k, σ, a, Ptop, Pbot, hRQ, kR, aR, hEll, hEllR, S, F, hF,
      T, Tstate] using hBessel.1
  · simpa [k, σ, a, Ptop, Pbot, hRQ, kR, aR, hEll, hEllR, S, F, hF,
      T, Tstate] using hBessel.2
  · calc
      pairedFluxImageMean (openCubeSet R) a
          (S + (-1 : ℝ) • pairedReflectState a Tstate) =
          volumeAverageVec (openCubeSet R) (fun x =>
            (blockMatVecMul (blockCoeffField a x) (S.eval x)).2) := by
              simpa [Tstate] using hFluxMean
      _ = volumeAverageVec (openCubeSet R)
          (smoothFeedbackCellAffineReciprocalGradient M m Q e ω) := hGammaMean

end

end ASDExplicitGamma.Scalar
