module

public import ASDExplicitGamma.Native.OldSignedLocalData
public import ASDExplicitGamma.Scalar.CoefficientFlux

/-! Actual cell projection removal and finite partition variation identities. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational

noncomputable section

/-- The restricted coefficient's chosen whole-plane display agrees with the
parent display at every point of the open cell. -/
theorem old_signed_cell_coefficient_extension_eq (Q R : TriadicCube 2)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (k : ResponseCoefficient (openCubeSet Q)) {x : Vec 2}
    (hx : x ∈ openCubeSet R) :
    responseCoefficientExtension (oldSignedCellCoefficient Q R hRQ k) x =
      responseCoefficientExtension k x := by
  rw [responseCoefficientExtension_eq (oldSignedCellCoefficient Q R hRQ k) hx,
    responseCoefficientExtension_eq k (hRQ hx)]
  simp only [oldSignedCellCoefficient, BoundedContinuousFunction.compContinuous_apply]
  rfl

/-- Normalized volume averages over a parent split exactly into the arithmetic
average of the normalized cell averages. -/
theorem old_signed_volumeAverage_descendants (Q : TriadicCube 2) (depth : ℕ)
    (f : Vec 2 → ℝ) (hf : IntegrableOn f (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) f =
      descendantsAverage Q depth (fun R => volumeAverage (openCubeSet R) f) := by
  have hfCube : IntegrableOn f (cubeSet Q) :=
    (integrableOn_cubeSet_iff_integrableOn_openCubeSet).2 hf
  have hCube := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    Q depth f hfCube
  have havg (R : TriadicCube 2) : volumeAverage (openCubeSet R) f = cubeAverage R f := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    rfl
  calc
    volumeAverage (openCubeSet Q) f = cubeAverage Q f := havg Q
    _ = descendantsAverage Q depth (fun R => cubeAverage R f) := hCube
    _ = descendantsAverage Q depth (fun R => volumeAverage (openCubeSet R) f) := by
      unfold descendantsAverage
      simp_rw [← havg]

/-- Scalar variation is invariant under changing its representative on a null set. -/
theorem old_signed_scalar_variation_congr_ae {U : Set (Vec 2)}
    {F G : Vec 2 → BlockVec 2}
    (hFG : F =ᵐ[volumeMeasureOn U] G)
    (hF : ScalarVariation U F) : ScalarVariation U G := by
  have hfst : (fun x => (F x).1) =ᵐ[volumeMeasureOn U]
      fun x => (G x).1 := hFG.mono fun x hx => congrArg Prod.fst hx
  have hsnd : (fun x => (F x).2) =ᵐ[volumeMeasureOn U]
      fun x => (G x).2 := hFG.mono fun x hx => congrArg Prod.snd hx
  refine ⟨hF.1.ae_eq hFG, hF.2.1.congr_ae hfst, ?_⟩
  intro φ
  calc
    ∫ x in U, vecDot (G x).2 (φ.grad x) ∂volume =
        ∫ x in U, vecDot (F x).2 (φ.grad x) ∂volume := by
      apply integral_congr_ae
      exact hsnd.mono fun x hx =>
        congrArg (fun v : Vec 2 => vecDot v (φ.grad x)) hx.symm
    _ = 0 := hF.2.2 φ

/-- A member of the closed correction space has a representative satisfying the
actual potential and zero-normal-trace conditions on an open cube. -/
theorem old_signed_hilbert_correction_variation (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (H : HilbertBlockL2 (openCubeSet Q))
    (hH : H ∈ (scalarFrameRealization Q nu sigma hnu hsigma k).correctionSpace.correctionSpace) :
    ScalarVariation (openCubeSet Q) (hilbertBlockL2ToBlockL2 H) := by
  let M : PotentialSolenoidalL2Data (openCubeSet Q) :=
    PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q)
  have hcanonical : H ∈ M.toMuCorrectionSpaceData.correctionSpace := by
    rw [← scalar_frame_correction_space Q nu sigma hnu hsigma k]
    exact hH
  let hRealize := PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
  let Rec : PotentialSolenoidalL2RecoveryData (openCubeSet Q) :=
    potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
      hRealize
  have hblockM : hilbertBlockL2ToBlockL2 H ∈ M.blockPotentialZeroTraceSolenoidalZeroNormalTrace :=
    (M.mem_toMuCorrectionSpaceData_iff H).1 hcanonical
  have hblockRec : hilbertBlockL2ToBlockL2 H ∈
      Rec.blockPotentialZeroTraceSolenoidalZeroNormalTrace := by
    change hilbertBlockL2ToBlockL2 H ∈ M.blockPotentialZeroTraceSolenoidalZeroNormalTrace
    exact hblockM
  let hc : Rec.toMuCorrectionSpaceData.correctionSpace.toSubmodule := ⟨H, by
    change hilbertBlockL2ToBlockL2 H ∈ Rec.blockPotentialZeroTraceSolenoidalZeroNormalTrace
    exact hblockRec⟩
  let hb := Rec.toBlockCorrectionSubmodule hc
  let data := Rec.repr hb
  have hdata : data.toBlockL2 = hilbertBlockL2ToBlockL2 H := by
    calc
      data.toBlockL2 = Rec.toBlockCorrectionSubmodule hc := Rec.repr_eq hb
      _ = hilbertBlockL2ToBlockL2 H := rfl
  have hdataAE : data.toBlockField =ᵐ[volumeMeasureOn (openCubeSet Q)]
      hilbertBlockL2ToBlockL2 H := by
    calc
      data.toBlockField =ᵐ[volumeMeasureOn (openCubeSet Q)] data.toBlockL2 :=
        (CorrectionFieldData.coeFn_toBlockL2 data).symm
      _ =ᵐ[volumeMeasureOn (openCubeSet Q)] hilbertBlockL2ToBlockL2 H := by
        rw [hdata]
  have hdataVariation : ScalarVariation (openCubeSet Q) data.toBlockField :=
    ⟨data.memBlockL2_toBlockField, data.isPotentialZeroTrace, data.isSolenoidalZeroNormalTrace⟩
  exact old_signed_scalar_variation_congr_ae hdataAE hdataVariation

/-- Removing the actual weighted cell minimizer from a source gives a genuine
zero-trace/zero-normal-trace variation on that cell. -/
theorem old_signed_cell_removed_variation (Q R : TriadicCube 2)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) :
    ScalarVariation (openCubeSet R)
      (fun x => F x - oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF x) := by
  let hFR : MemBlockL2 (openCubeSet R) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hRQ)
  let H : HilbertBlockL2 (openCubeSet R) := toHilbertBlockL2OfBlockField hFR
  let Z : Vec 2 → BlockVec 2 := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF
  have hZ : MemBlockL2 (openCubeSet R) Z := (oldSignedCellResidual Q R hRQ
    nu sigma hnu hsigma k F hF).property
  let hY : MemBlockL2 (openCubeSet R) (fun x => F x - Z x) := hFR.sub hZ
  have hYblock : toBlockL2 hY = toBlockL2 hFR - toBlockL2 hZ := by
    apply Lp.ext
    filter_upwards [coeFn_toBlockL2 hY, coeFn_toBlockL2 hFR, coeFn_toBlockL2 hZ,
      (Lp.coeFn_sub (toBlockL2 hFR) (toBlockL2 hZ))] with x hy hf hz hsub
    rw [hy, hsub]
    change F x - Z x = toBlockL2 hFR x - toBlockL2 hZ x
    rw [hf, hz]
  have hZhilbert : toHilbertBlockL2OfBlockField hZ =
      scalarProjectionResidual R nu sigma hnu hsigma
        (oldSignedCellCoefficient Q R hRQ k) H := by
    change toHilbertBlockL2OfBlockField
      (Lp.memLp (hilbertBlockL2ToBlockL2
        (scalarProjectionResidual R nu sigma hnu hsigma
          (oldSignedCellCoefficient Q R hRQ k) H))) = _
    exact hilbert_field_rebuild _
  have hYhilbert : toHilbertBlockL2OfBlockField hY = H -
      scalarProjectionResidual R nu sigma hnu hsigma
        (oldSignedCellCoefficient Q R hRQ k) H := by
    calc
      toHilbertBlockL2OfBlockField hY = blockL2ToHilbertBlockL2 (toBlockL2 hY) :=
        (blockL2ToHilbertBlockL2_toBlockL2 hY).symm
      _ = blockL2ToHilbertBlockL2 (toBlockL2 hFR) - blockL2ToHilbertBlockL2 (toBlockL2 hZ) := by
        rw [hYblock, map_sub]
      _ = H - scalarProjectionResidual R nu sigma hnu hsigma
          (oldSignedCellCoefficient Q R hRQ k) H := by
        rw [blockL2ToHilbertBlockL2_toBlockL2 hFR,
          blockL2ToHilbertBlockL2_toBlockL2 hZ, hZhilbert]
  have hmem : toHilbertBlockL2OfBlockField hY ∈
      (scalarFrameRealization R nu sigma hnu hsigma
        (oldSignedCellCoefficient Q R hRQ k)).correctionSpace.correctionSpace := by
    rw [hYhilbert]
    exact scalar_projection_removed_mem R nu sigma hnu hsigma
      (oldSignedCellCoefficient Q R hRQ k) H
  have hrep : toBlockL2 hY = hilbertBlockL2ToBlockL2
      (toHilbertBlockL2OfBlockField hY) :=
    (hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField hY).symm
  have hYae : (fun x => F x - Z x) =ᵐ[volumeMeasureOn (openCubeSet R)]
      hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hY) := by
    calc
      (fun x => F x - Z x) =ᵐ[volumeMeasureOn (openCubeSet R)] toBlockL2 hY :=
        (coeFn_toBlockL2 hY).symm
      _ =ᵐ[volumeMeasureOn (openCubeSet R)]
          hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hY) := by rw [hrep]
  exact old_signed_scalar_variation_congr_ae hYae.symm
    (old_signed_hilbert_correction_variation R nu sigma hnu hsigma
      (oldSignedCellCoefficient Q R hRQ k)
      (toHilbertBlockL2OfBlockField hY) hmem)

/-- The sum of the actual cellwise zero-trace corrections is the parent source
minus the finite piecewise weighted residual, almost everywhere. -/
theorem old_signed_local_removed_variation (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) :
    ScalarVariation (openCubeSet Q)
      (fun x => F x - oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF x) := by
  classical
  let D := {R : TriadicCube 2 // R ∈ descendantsAtDepth Q depth}
  let cellCorrection (R : D) : Vec 2 → BlockVec 2 := fun x =>
    F x - oldSignedCellResidual Q R.1
      (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
      nu sigma hnu hsigma k F hF x
  have hcell (R : D) : ScalarVariation (openCubeSet Q)
      ((openCubeSet R.1).indicator (cellCorrection R)) := by
    exact scalar_variation_zero_extension (isOpen_openCubeSet R.1)
      (isOpen_openCubeSet Q)
      (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
      (old_signed_cell_removed_variation Q R.1
        (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
        nu sigma hnu hsigma k F hF)
  have hsumVariation (s : Finset D) : ScalarVariation (openCubeSet Q)
      (fun x => ∑ R ∈ s, (openCubeSet R.1).indicator (cellCorrection R) x) := by
    induction s using Finset.induction_on with
    | empty =>
        have hz : (fun _ : Vec 2 => (0 : BlockVec 2)) = 0 := by
          funext x
          simp
        simp only [Finset.sum_empty]
        rw [hz]
        exact scalar_variation_zero (openCubeSet Q)
    | @insert R s hR hs =>
        have hadd := scalar_variation_add (hcell R) hs
        have hsum :
            (fun x => ∑ T ∈ insert R s,
              (openCubeSet T.1).indicator (cellCorrection T) x) =
              (openCubeSet R.1).indicator (cellCorrection R) +
                (fun x => ∑ T ∈ s, (openCubeSet T.1).indicator (cellCorrection T) x) := by
          funext x
          rw [Finset.sum_insert hR]
          rfl
        rw [hsum]
        exact hadd
  have hsumVar : ScalarVariation (openCubeSet Q)
      (fun x => ∑ R : D, (openCubeSet R.1).indicator (cellCorrection R) x) := by
    simpa only [Finset.sum_apply] using hsumVariation Finset.univ
  have hnotBoundary : ∀ᵐ x ∂volume, ∀ R : D, x ∉ cubeBoundary R.1 := by
    rw [ae_all_iff]
    intro R
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using volume_cubeBoundary_eq_zero R.1
  have hAE : (fun x => F x - oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF x) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => ∑ R : D, (openCubeSet R.1).indicator (cellCorrection R) x := by
    apply (ae_restrict_iff' (measurableSet_openCubeSet Q)).2
    filter_upwards [hnotBoundary] with x hnb hxQ
    obtain ⟨R, hR, hxCube⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet depth
      (openCubeSet_subset_cubeSet Q hxQ)
    have hxOpen : x ∈ openCubeSet R := by
      by_contra hxR
      exact hnb ⟨R, hR⟩ ⟨hxCube, hxR⟩
    let i : D := ⟨R, hR⟩
    have hresidual : oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF x =
        oldSignedCellResidual Q R (openCubeSet_subset_of_mem_descendantsAtDepth hR)
          nu sigma hnu hsigma k F hF x := by
      change (∑ S : D, (openCubeSet S.1).indicator
        (oldSignedCellResidual Q S.1
          (openCubeSet_subset_of_mem_descendantsAtDepth S.2)
          nu sigma hnu hsigma k F hF) x) = _
      rw [Fintype.sum_eq_single i]
      · rw [Set.indicator_of_mem (by simpa [i] using hxOpen)]
      · intro S hSi
        have hne : S.1 ≠ R := by
          intro heq
          apply hSi
          exact Subtype.ext heq
        have hdisj := pairwiseDisjoint_openCubeSet_descendantsAtDepth Q depth S.2 hR hne
        have hxS : x ∉ openCubeSet S.1 := fun hxS =>
          (Set.disjoint_left.mp hdisj) hxS hxOpen
        simp [hxS]
    have hcorrection :
        (∑ S : D, (openCubeSet S.1).indicator (cellCorrection S) x) =
          F x - oldSignedCellResidual Q R
            (openCubeSet_subset_of_mem_descendantsAtDepth hR)
            nu sigma hnu hsigma k F hF x := by
      rw [Fintype.sum_eq_single i]
      · rw [Set.indicator_of_mem (by simpa [i] using hxOpen)]
      · intro S hSi
        have hne : S.1 ≠ R := by
          intro heq
          apply hSi
          exact Subtype.ext heq
        have hdisj := pairwiseDisjoint_openCubeSet_descendantsAtDepth Q depth S.2 hR hne
        have hxS : x ∉ openCubeSet S.1 := fun hxS =>
          (Set.disjoint_left.mp hdisj) hxS hxOpen
        simp [hxS]
    rw [hresidual]
    exact hcorrection.symm
  exact old_signed_scalar_variation_congr_ae hAE.symm hsumVar

/-- The parent energy of the finite piecewise residuals is exactly the average
of their actual normalized cell energies. -/
theorem old_signed_local_residual_energy (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F G : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k G hG) =
    descendantsAverage Q depth (fun R =>
      volumeAverage (openCubeSet R) (fun x =>
        blockVecDot
          (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF x)
          (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
            (oldSignedLocalResidual Q depth nu sigma hnu hsigma k G hG x)))) := by
  let LF := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
  let LG := oldSignedLocalResidual Q depth nu sigma hnu hsigma k G hG
  let a := responseFramePlanarCoefficientField nu sigma k
  let f : Vec 2 → ℝ := fun x => blockVecDot (LF x)
    (blockMatVecMul (blockCoeffField a x) (LG x))
  have hLF : MemBlockL2 (openCubeSet Q) LF :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k F hF
  have hLG : MemBlockL2 (openCubeSet Q) LG :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k G hG
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  let XF : BlockState 2 := ⟨fun x => (LF x).1, fun x => (LF x).2⟩
  let XG : BlockState 2 := ⟨fun x => (LG x).1, fun x => (LG x).2⟩
  have hpair : blockPairingIntegrand a XF XG = f := by
    funext x
    simp [blockPairingIntegrand, XF, XG, BlockState.eval, f]
  have hf : IntegrableOn f (openCubeSet Q) := by
    have hflux := scalar_coefficient_flux_memL2 Q a hEll hLG
    have hfirst := integrableOn_vecDot_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2 hLF) (memVectorL2_fst_of_memBlockL2 hflux)
    have hsecond := integrableOn_vecDot_of_memVectorL2
      (memVectorL2_snd_of_memBlockL2 hLF) (memVectorL2_snd_of_memBlockL2 hflux)
    have hsum : IntegrableOn (fun x =>
        vecDot (LF x).1 (scalarCoefficientFlux a LG x).1 +
        vecDot (LF x).2 (scalarCoefficientFlux a LG x).2) (openCubeSet Q) :=
      hfirst.add hsecond
    exact hsum.congr_fun_ae <| (Filter.Eventually.of_forall fun x => by
      simp [f, scalarCoefficientFlux, blockVecDot])
  have hpartition := old_signed_volumeAverage_descendants Q depth f hf
  unfold oldSignedEnergyPairing
  change volumeAverage (openCubeSet Q) f =
    descendantsAverage Q depth (fun R => volumeAverage (openCubeSet R) f)
  exact hpartition

/-- Cross pairings of L2 fields against the actual bounded coefficient are
integrable on a triadic square. -/
private theorem old_signed_block_pairing_integrable (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F G : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    IntegrableOn (fun x => blockVecDot (F x)
      (blockMatVecMul (blockCoeffField a x) (G x))) (openCubeSet Q) := by
  have hflux := scalar_coefficient_flux_memL2 Q a hEll hG
  have hfirst := integrableOn_vecDot_of_memVectorL2
    (memVectorL2_fst_of_memBlockL2 hF) (memVectorL2_fst_of_memBlockL2 hflux)
  have hsecond := integrableOn_vecDot_of_memVectorL2
    (memVectorL2_snd_of_memBlockL2 hF) (memVectorL2_snd_of_memBlockL2 hflux)
  have hsum : IntegrableOn (fun x =>
      vecDot (F x).1 (scalarCoefficientFlux a G x).1 +
      vecDot (F x).2 (scalarCoefficientFlux a G x).2) (openCubeSet Q) :=
    hfirst.add hsecond
  exact hsum.congr_fun_ae <| Filter.Eventually.of_forall fun x => by
    simp [scalarCoefficientFlux, blockVecDot]

/-- The finite local minimizers pair against every source exactly as the source
itself does. The proof applies the genuine local projection orthogonality on
each descendant and sums over the partition. -/
theorem old_signed_local_residual_pairing (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F G : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k G hG) =
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF) G := by
  classical
  let LF := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
  let LG := oldSignedLocalResidual Q depth nu sigma hnu hsigma k G hG
  let a := responseFramePlanarCoefficientField nu sigma k
  let d : Vec 2 → ℝ := fun x => blockVecDot (LF x)
    (blockMatVecMul (blockCoeffField a x) (G x - LG x))
  have hLF : MemBlockL2 (openCubeSet Q) LF :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k F hF
  have hLG : MemBlockL2 (openCubeSet Q) LG :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k G hG
  have hGminus : MemBlockL2 (openCubeSet Q) (fun x => G x - LG x) := hG.sub hLG
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hdInt := old_signed_block_pairing_integrable Q a hEll LF
    (fun x => G x - LG x) hLF hGminus
  have hCellZero : ∀ R, R ∈ descendantsAtDepth Q depth →
      volumeAverage (openCubeSet R) d = 0 := by
    intro R hR
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField nu sigma kR
    let ZF := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF
    let ZG := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k G hG
    have hLFae := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k F hF R hR
    have hLGae := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k G hG R hR
    have hGvar := old_signed_cell_removed_variation Q R hRQ nu sigma hnu hsigma k G hG
    have horthField := scalar_residual_field_orthogonal R nu sigma hnu hsigma kR
      (toHilbertBlockL2OfBlockField
        (hF.mono_measure (Measure.restrict_mono_set volume hRQ)))
      (fun x => G x - ZG x) hGvar
    have horth : volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (G x - ZG x)
          (blockMatVecMul (blockCoeffField aR x) (ZF x))) = 0 := by
      simpa [ZF, ZG, aR, kR, oldSignedCellResidual] using horthField
    have hcoeff (x : Vec 2) (hx : x ∈ openCubeSet R) :
        blockCoeffField aR x = blockCoeffField a x := by
      simp only [aR, a, responseFramePlanarCoefficientField, blockCoeffField]
      rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
    have hpoint (x : Vec 2) (hx : x ∈ openCubeSet R) :
        blockVecDot (ZF x)
          (blockMatVecMul (blockCoeffField a x) (G x - ZG x)) =
        blockVecDot (G x - ZG x)
          (blockMatVecMul (blockCoeffField aR x) (ZF x)) := by
      rw [hcoeff x hx]
      simpa [blockCoeffField] using
        (blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm
          (a x) (ZF x) (G x - ZG x))
    have hDAE : d =ᵐ[volumeMeasureOn (openCubeSet R)]
        (fun x => blockVecDot (G x - ZG x)
          (blockMatVecMul (blockCoeffField aR x) (ZF x))) := by
      filter_upwards [hLFae, hLGae,
        ae_restrict_mem (measurableSet_openCubeSet R)] with x hLFx hLGx hx
      change blockVecDot (LF x)
          (blockMatVecMul (blockCoeffField a x) (G x - LG x)) = _
      dsimp only [LF, LG]
      rw [hLFx, hLGx]
      exact hpoint x hx
    have hIntegral := integral_congr_ae hDAE
    unfold volumeAverage at horth ⊢
    rw [hIntegral]
    exact horth
  have hpartition := old_signed_volumeAverage_descendants Q depth d hdInt
  have hsumZero : descendantsAverage Q depth
      (fun R => volumeAverage (openCubeSet R) d) = 0 := by
    unfold descendantsAverage
    change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
      (descendantsAtDepth Q depth).sum (fun R => volumeAverage (openCubeSet R) d) = 0
    rw [Finset.sum_eq_zero]
    · simp
    · intro R hR
      exact hCellZero R hR
  have hdavg : volumeAverage (openCubeSet Q) d = 0 := hpartition.trans hsumZero
  let f : Vec 2 → ℝ := fun x => blockVecDot (LF x)
    (blockMatVecMul (blockCoeffField a x) (G x))
  let g : Vec 2 → ℝ := fun x => blockVecDot (LF x)
    (blockMatVecMul (blockCoeffField a x) (LG x))
  have hf := old_signed_block_pairing_integrable Q a hEll LF G hLF hG
  have hg := old_signed_block_pairing_integrable Q a hEll LF LG hLF hLG
  have hsubFun : (fun x => f x - g x) = d := by
    funext x
    simp [f, g, d, blockVecDot, vecDot, blockMatVecMul, matVecMul,
      Fin.sum_univ_two]
    ring
  have hsub := volumeAverage_sub hf hg
  have hsub' : volumeAverage (openCubeSet Q) f -
      volumeAverage (openCubeSet Q) g = volumeAverage (openCubeSet Q) d := by
    calc
      _ = volumeAverage (openCubeSet Q) (fun x => f x - g x) := hsub.symm
      _ = volumeAverage (openCubeSet Q) d := by rw [hsubFun]
  have hfg : volumeAverage (openCubeSet Q) f =
      volumeAverage (openCubeSet Q) g := by
    exact sub_eq_zero.mp (hsub'.trans hdavg)
  simpa [f, g, LF, LG, a, oldSignedEnergyPairing] using hfg.symm

end

end ASDExplicitGamma.Native
