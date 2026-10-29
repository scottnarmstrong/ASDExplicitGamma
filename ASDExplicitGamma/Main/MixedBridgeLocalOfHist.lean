module

public import ASDExplicitGamma.Main.MixedBridgeDepthFive

/-! Successor of `mixed_bridge_local_parent_gap_rows` with the history envelope `Hfun`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Cold ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

local instance mixedBridgeLocalCubeCompact_ofHist (U : TriadicCube 2) :
    CompactSpace (closure (cubeSet U)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet U).isCompact_closure

private theorem mixed_bridge_local_parent_canonical_cell_residual_eq
    (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedCellResidual Q U hU nu sigma hnu hsigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)) =ᵐ[
        volumeMeasureOn (openCubeSet U)]
      oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P := by
  let kU := oldSignedCellCoefficient Q U hU k
  let F := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
  let hF : MemBlockL2 (openCubeSet Q) F := Lp.memLp F
  let hFU : MemBlockL2 (openCubeSet U) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hU)
  let X : HilbertBlockL2 (openCubeSet U) := toHilbertBlockL2OfBlockField hFU
  let D := scalarFrameEnergyData U nu sigma hnu hsigma kU
  let K := scalarFrameVariationSpace U nu sigma hnu hsigma kU
  have hXfield : hilbertBlockL2ToBlockL2 X =ᵐ[volumeMeasureOn (openCubeSet U)] F := by
    rw [hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField hFU]
    exact coeFn_toBlockL2 hFU
  have hparent : scalarResidualField Q nu sigma hnu hsigma k
      ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) = F := by
    rw [old_signed_affine_residual_field]
    rfl
  have hproj : K.toSubmodule.starProjection (responseEnergyUp D X) = 0 := by
    apply K.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact K.toSubmodule.zero_mem
    · intro Y hY
      let hYmem : Y.down ∈
          (scalarFrameRealization U nu sigma hnu hsigma kU).correctionSpace.correctionSpace := hY
      let Yfield := hilbertBlockL2ToBlockL2 Y.down
      have hYvariation : ScalarVariation (openCubeSet U) Yfield :=
        old_signed_hilbert_correction_variation U nu sigma hnu hsigma kU
          Y.down hYmem
      have hYfield : MemBlockL2 (openCubeSet U) Yfield := Yfield.property
      have hYrebuild : toHilbertBlockL2OfBlockField hYfield = Y.down :=
        hilbert_field_rebuild _
      have horth := scalar_residual_local_orthogonal Q U hU nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)
        Yfield hYvariation
      have hcoeff := old_signed_cell_frame_coefficient_ae Q U hU nu sigma k
      have havg : volumeAverage (openCubeSet U) (fun x =>
          blockVecDot (Yfield x)
            (blockMatVecMul (blockCoeffField
              (responseFramePlanarCoefficientField nu sigma kU) x) (F x))) =
          volumeAverage (openCubeSet U) (fun x =>
          blockVecDot (Yfield x)
            (blockMatVecMul (blockCoeffField
              (responseFramePlanarCoefficientField nu sigma k) x)
              ((scalarResidualField Q nu sigma hnu hsigma k
                ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x))) := by
        unfold volumeAverage
        congr 1
        apply integral_congr_ae
        filter_upwards [hcoeff] with x hax
        have hax' : responseFramePlanarCoefficientField nu sigma kU x =
            responseFramePlanarCoefficientField nu sigma k x := by
          simpa [kU] using hax
        have haxBlock : blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x =
            blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x := by
          simpa [blockCoeffField] using congrArg blockMatrixOfCoeff hax'
        have hparentx :
            (scalarResidualField Q nu sigma hnu hsigma k
              ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x = F x :=
          congrArg (fun f : BlockL2 (openCubeSet Q) => f x) hparent
        rw [haxBlock, ← hparentx]
      have hbil := scalar_frame_bilinear_field U nu sigma hnu hsigma kU hFU hYfield
      rw [hYrebuild] at hbil
      rw [sub_zero]
      change (scalarFrameRealization U nu sigma hnu hsigma kU).energyBilin X Y.down = 0
      rw [hbil]
      exact havg.trans horth
  have hres : scalarProjectionResidual U nu sigma hnu hsigma kU X = X := by
    change (responseEnergyUp D X -
      K.toSubmodule.starProjection (responseEnergyUp D X)).down = X
    rw [hproj]
    simp [responseEnergyUp_down]
  change hilbertBlockL2ToBlockL2
    (scalarProjectionResidual U nu sigma hnu hsigma kU X) =ᵐ[
      volumeMeasureOn (openCubeSet U)] F
  rw [hres]
  exact hXfield

private theorem mixed_bridge_local_first_corrector_grad_zero
    (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P))).toH1Function.grad =ᵐ[
        volumeMeasureOn (openCubeSet U)] 0 := by
  rw [old_signed_cell_first_corrector_grad]
  have hres := mixed_bridge_local_parent_canonical_cell_residual_eq
    Q U hU nu sigma hnu hsigma k P
  filter_upwards [hres] with x hx
  have hfirst :
      (oldSignedCellResidual Q U hU nu sigma hnu hsigma k
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
        (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)) x).1 =
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1 :=
    congrArg Prod.fst hx
  change (oldSignedCellResidual Q U hU nu sigma hnu hsigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)) x).1 -
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1 = 0
  exact sub_eq_zero.mpr hfirst

private theorem mixed_bridge_local_vectorWeakHaarNorm_zero
    (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : F =ᵐ[volumeMeasureOn (openCubeSet Q)] 0) :
    vectorWeakHaarNorm Q F = 0 := by
  have hF' : F =ᵐ[volume.restrict (cubeSet Q)] 0 := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact hF
  have hcoord (i : Fin 2) : (fun x => F x i) =ᵐ[volume.restrict (cubeSet Q)] 0 := by
    filter_upwards [hF'] with x hx
    exact congrArg (fun v : Vec 2 => v i) hx
  have hzeroProj (j : ℕ) : cubeProjection Q j (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
    funext x
    simp [cubeProjection, cubeAverage_const]
  unfold vectorWeakHaarNorm
  have hEnergy : vectorWeakHaarEnergy Q F =
      vectorWeakHaarEnergy Q (fun _ : Vec 2 => (0 : Vec 2)) := by
    unfold vectorWeakHaarEnergy
    apply Finset.sum_congr rfl
    intro i hi
    unfold dualEnergy
    exact diagPrimalEnergy_congr_ae Q (Real.sqrt 3)⁻¹ (hcoord i)
  rw [hEnergy]
  simp [vectorWeakHaarEnergy, dualEnergy, primalEnergy, energy, pairing,
    cubeIncrement_zero, cubeIncrement_succ, hzeroProj, cubeAverage_const]

private theorem mixed_bridge_local_corrector_square_zero'
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) (V : SquareCells U j) :
    mixedBridgeLocalCorrectorSq' M m U t ω j V = 0 := by
  classical
  unfold mixedBridgeLocalCorrectorSq'
  apply Finset.sum_eq_zero
  intro a ha
  have hV : openCubeSet V.val ⊆ openCubeSet U :=
    openCubeSet_subset_of_mem_descendantsAtDepth V.property
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let k := mainAffineOpenResponseRestriction U
    (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  have hgrad := mixed_bridge_local_first_corrector_grad_zero
    U V.val hV M.nu σ M.nu_pos hσ k (blockBasis a)
  rw [mixed_bridge_local_vectorWeakHaarNorm_zero V.val hgrad]
  simp

private theorem mixed_bridge_local_depth_square_zero
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    mixedBridgeVLocalDepthSq' M m U t ω j = 0 := by
  classical
  unfold mixedBridgeVLocalDepthSq' Cold.squareCellMean
  have hsum : ∑ V : SquareCells U j,
      mixedBridgeLocalCorrectorSq' M m U t ω j V = 0 := by
    apply Finset.sum_eq_zero
    intro V hV
    exact mixed_bridge_local_corrector_square_zero' M m U t ω j V
  rw [hsum]
  simp

private theorem mixed_bridge_local_vl2_zero
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    mixedBridgeVl2Local M m U t ω = 0 := by
  unfold mixedBridgeVl2Local
  have hz (j : ℕ) : mixedBridgeVLocalDepthSq' M m U t ω j = 0 :=
    mixed_bridge_local_depth_square_zero M m U t ω j
  simp_rw [hz]
  simp

attribute [local irreducible] Homogenization.descendantsAtDepth
theorem mixed_bridge_local_Vl_bound (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (Hfun : ℝ → ℝ) (xi : ℝ) (hH : 0 ≤ Hfun t) (hxi : 0 ≤ xi) :
    Integrable (fun ω => mixedGlobalHistoryMax M m t ω * mixedBridgeVlLocal M m U t ω ^ 2)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, mixedGlobalHistoryMax M m t ω * mixedBridgeVlLocal M m U t ω ^ 2
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      mainBeta * xi + mainEpsNew * mainD * mainBeta * Hfun t := by
  have hVlZero (ω : Cutoff.CutoffSample 2) : mixedBridgeVlLocal M m U t ω ^ 2 = 0 := by
    simp [mixedBridgeVlLocal, mixed_bridge_local_vl2_zero]
  have heq : (fun ω => mixedGlobalHistoryMax M m t ω * mixedBridgeVlLocal M m U t ω ^ 2) =
      fun _ : Cutoff.CutoffSample 2 => 0 := by
    funext ω
    rw [hVlZero ω]
    ring
  rw [heq]
  refine ⟨integrable_const 0, ?_⟩
  simp only [integral_const, smul_zero]
  have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
  have hε : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
  have hAlpha : 0 ≤ mainAlpha := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hD : 0 ≤ mainD := by
    dsimp [mainD]
    exact add_nonneg (by norm_num) hAlpha
  positivity

/-- Successor of `mixed_bridge_local_parent_gap_rows` with the history envelope `Hfun`. -/
theorem mixed_bridge_local_parent_gap_rows_ofHist'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 m) 5)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    let B : Cutoff.CutoffSample 2 → ℝ := mixedGlobalHistoryMax M m t
    let V : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVLocal M m U t
    let G : Cutoff.CutoffSample 2 → ℝ := mixedBridgeGLocal M m U t
    let Vl : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVlLocal M m U t
    let f_U := ∫ ω, rawCubeFourLoadTrace M m U t ω ∂μ
    Integrable (fun ω => V ω ^ 2) μ ∧
    (∫ ω, V ω ^ 2 ∂μ) ≤ xi - mainBetaOld * f_U ∧
    (∀ k : Fin 4,
      Integrable (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ ∧
      (∫ ω, B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ∂μ) ≤
        2 * mainBeta ^ k.val * xi) ∧
    Integrable (fun ω => B ω * G ω ^ 2) μ ∧
    (∫ ω, B ω * G ω ^ 2 ∂μ) ≤ 2 * mainBeta * xi ∧
    Integrable (fun ω => B ω * Vl ω ^ 2) μ ∧
    (∫ ω, B ω * Vl ω ^ 2 ∂μ) ≤
      mainBeta * xi + mainEpsNew * mainD * mainBeta *
        Hfun t := by
  have hmain := mixed_bridge_local_parent_gap_rows M h hM hγ N hpast m hm t ht U hU
  have hH : 0 ≤ Hfun t := le_trans (lpNorm_nonneg) (hHist t ht).2.2
  have hxi : 0 ≤ mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma mainSourceInversePrefix (theta M) t := by
    have hpre : 0 ≤ mainSourceInversePrefix := by
      have hbeta : 0 < mainBetaOld / 100 := by norm_num [mainBetaOld]
      exact le_of_lt (lt_trans hbeta mainSourceInversePrefix_gate)
    exact hpre.trans (mainEnvelopeXi_ge_initial (sq_nonneg _)
      M.shellPrefix.gamma_pos.le hγ (ASDExplicitGamma.Cold.cold_theta_pos M).le ht.1)
  have hVl := mixed_bridge_local_Vl_bound M m U t Hfun _ hH hxi
  exact ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2.1, hVl.1, hVl.2⟩

end
end ASDExplicitGamma.Main
end
