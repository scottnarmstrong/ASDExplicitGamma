module

public import ASDExplicitGamma.Main.HotObsLocalHelpers
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit

/-! Observer-cell version of the local OLD parent-gap rows. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Cold ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

local instance mixedBridgeLocalCubeCompact'' (U : TriadicCube 2) :
    CompactSpace (closure (cubeSet U)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet U).isCompact_closure

attribute [local irreducible] Homogenization.descendantsAtDepth

theorem mixed_bridge_local_parent_canonical_cell_residual_eq'
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

theorem mixed_bridge_local_first_corrector_grad_zero'
    (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P))).toH1Function.grad =ᵐ[
        volumeMeasureOn (openCubeSet U)] 0 := by
  rw [old_signed_cell_first_corrector_grad]
  have hres := mixed_bridge_local_parent_canonical_cell_residual_eq'
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

theorem mixed_bridge_local_vectorWeakHaarNorm_zero'
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

theorem mixed_bridge_local_corrector_square_zero''
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
  have hgrad := mixed_bridge_local_first_corrector_grad_zero'
    U V.val hV M.nu σ M.nu_pos hσ k (blockBasis a)
  rw [mixed_bridge_local_vectorWeakHaarNorm_zero' V.val hgrad]
  simp

theorem mixed_bridge_local_depth_square_zero'
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    mixedBridgeVLocalDepthSq' M m U t ω j = 0 := by
  classical
  unfold mixedBridgeVLocalDepthSq' Cold.squareCellMean
  have hsum : ∑ V : SquareCells U j,
      mixedBridgeLocalCorrectorSq' M m U t ω j V = 0 := by
    apply Finset.sum_eq_zero
    intro V hV
    exact mixed_bridge_local_corrector_square_zero'' M m U t ω j V
  rw [hsum]
  simp

theorem mixed_bridge_local_vl2_zero'
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    mixedBridgeVl2Local M m U t ω = 0 := by
  unfold mixedBridgeVl2Local
  have hz (j : ℕ) : mixedBridgeVLocalDepthSq' M m U t ω j = 0 :=
    mixed_bridge_local_depth_square_zero' M m U t ω j
  simp_rw [hz]
  simp

theorem mixed_bridge_local_pointwise_rows'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hUObserver : U ∈ bankObserverRoots (originCube 2 (m + 40)) 5) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mixedBridgeVLocal M m U t ω ^ 2 ≤
        mixedOldTheta M m U t ω - mainBetaOld * rawCubeFourLoadTrace M m U t ω ∧
      mixedBridgeVLocal M m U t ω ^ 2 + mixedBridgeGLocal M m U t ω ^ 2 ≤
        2 * mixedOldTheta M m U t ω := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let σ : ℝ := Annealed.sigmaBar M m
  let k (ω : Cutoff.CutoffSample 2) : ResponseCoefficient (openCubeSet U) :=
    mainAffineOpenResponseRestriction U
      (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  let a (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
    responseFramePlanarCoefficientField M.nu σ (k ω)
  let C (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
    mixedOldDepthCoefficient M m t j ω
  let D (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
    lemmaVInverseDepthMax U (a ω) j
  let T (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
    rawWeakTraceSequence M m U t ω j
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hEll (ω : Cutoff.CutoffSample 2) :
      IsEllipticFieldOn (M.nu / σ)
        (((M.nu / σ) ^ 2 + (‖k ω‖ / σ) ^ 2) / (M.nu / σ))
        (openCubeSet U) (a ω) := by
    exact responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet U) M.nu σ M.nu_pos hσ (k ω)
  have htrace (ω : Cutoff.CutoffSample 2) (j : ℕ) :
      descendantsAverage U j (fun V => traceDefect (openCubeSet V) (a ω) 1) = T j ω := by
    simpa [T, a, k, σ] using
      mixed_bridge_local_trace_average_eq' M m t ht U ω j
  have hparentTrace (ω : Cutoff.CutoffSample 2) :
      traceDefect (openCubeSet U) (a ω) 1 = rawCubeFourLoadTrace M m U t ω := by
    have h0 := htrace ω 0
    have hAvg : descendantsAverage U 0
        (fun V => traceDefect (openCubeSet V) (a ω) 1) =
          traceDefect (openCubeSet U) (a ω) 1 := by
      simp [descendantsAverage, Homogenization.descendantsAtDepth_zero]
    have hTzero : T 0 ω = rawCubeFourLoadTrace M m U t ω := by
      change Cold.squareCellMean U 0
        (fun C => rawCubeFourLoadTrace M m C.1 t ω) = _
      rw [mixed_bridge_local_squareCellMean_eq_descendantsAverage' U 0
        (fun V => rawCubeFourLoadTrace M m V t ω)]
      simp [descendantsAverage, Homogenization.descendantsAtDepth_zero]
    rw [hAvg, hTzero] at h0
    exact h0
  have hdepth (j : ℕ) : ∀ᵐ ω ∂μ, D j ω ≤ C j ω := by
    simpa only [D, C, a, k, σ, μ] using
      mixed_bridge_local_depth_inverse_max_bound'
        M h hM hγ N hpast m hm t ht U hUObserver j
  have hdepthAll : ∀ᵐ ω ∂μ, ∀ j : ℕ, D j ω ≤ C j ω := by
    apply ae_all_iff.mpr
    intro j
    exact hdepth j
  have hθSum (ω : CutoffSample 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * C j ω * T j ω) := by
    have hEllω := hEll ω
    have htraceω (j : ℕ) := htrace ω j
    simpa [C, T, α] using mixed_bridge_local_theta_core_summable'
      M m t ht ω U (a ω) hEllω htraceω hγ
  have hθSumRight (ω : CutoffSample 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * (C j ω * T j ω)) := by
    simpa only [← mul_assoc] using hθSum ω
  have hCoeffSum (ω : CutoffSample 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * C j ω) := by
    simpa [C, α] using mixed_bridge_local_coefficient_summable'
      M m t ht ω hγ
  have hq0 : 0 ≤ α ^ 2 := sq_nonneg α
  have hq1 : α ^ 2 < 1 := by
    nlinarith [Scalar.inverse_history_discount_range.1,
      Scalar.inverse_history_discount_range.2]
  have hWsum : Summable (fun j : ℕ => (1 - α ^ 2) * α ^ (2 * j)) := by
    have hα := Scalar.inverse_history_discount_range
    have hgeom := summable_geometric_of_lt_one hq0 hq1
    have hh := hgeom.mul_left (1 - α ^ 2)
    apply hh.congr
    intro j
    simp [pow_mul]
  have hWtotal : ∑' j : ℕ, (1 - α ^ 2) * α ^ (2 * j) = 1 := by
    let q : ℝ := α ^ 2
    have hq0 : 0 ≤ q := sq_nonneg α
    have hq1 : q < 1 := by
      dsimp [q]
      nlinarith [Scalar.inverse_history_discount_range.1,
        Scalar.inverse_history_discount_range.2]
    have hsum : ∑' j : ℕ, q ^ j = (1 - q)⁻¹ :=
      tsum_geometric_of_lt_one hq0 hq1
    calc
      _ = ∑' j : ℕ, (1 - q) * q ^ j := by
        apply tsum_congr
        intro j
        simp [q, pow_mul]
      _ = (1 - q) * ∑' j : ℕ, q ^ j := tsum_mul_left
      _ = 1 := by rw [hsum]; exact mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hq1))
  have hCnonneg (j : ℕ) (ω : CutoffSample 2) : 0 ≤ C j ω := by
    rw [show C j ω = mixedOldDepthCoefficient M m t j ω by rfl,
      mixed_old_depth_coefficient_formula]
    change 0 ≤ (3683 / 2500 : ℝ) * (3 : ℝ) ^
      (2 * M.gamma * (j : ℝ)) + positiveSplitRemainder _ _ _
    exact add_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (by norm_num) _)) ((positive_split _ _ _).1)
  have hCminor (j : ℕ) (ω : CutoffSample 2) : mainBetaOld ≤ C j ω := by
    rw [show C j ω = mixedOldDepthCoefficient M m t j ω by rfl,
      mixed_old_depth_coefficient_formula]
    have hpow : 1 ≤ (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity [M.shellPrefix.gamma_pos])
    have hR : 0 ≤ mixedOldLocalDepthRemainder M m t j ω := by
      change 0 ≤ positiveSplitRemainder _ _ _
      exact (positive_split _ _ _).1
    dsimp [mainBetaOld]
    nlinarith [mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 3683 / 2500)]
  have hWcoeffSum (ω : CutoffSample 2) :
      Summable (fun j : ℕ => ((1 - α ^ 2) * α ^ (2 * j)) * C j ω) := by
    have hh := (hCoeffSum ω).mul_left (1 - α ^ 2)
    apply hh.congr
    intro j
    ring
  have hmassLower (ω : CutoffSample 2) :
      mainBetaOld ≤ ∑' j : ℕ, ((1 - α ^ 2) * α ^ (2 * j)) * C j ω := by
    have hbaseSum : Summable (fun j : ℕ =>
        ((1 - α ^ 2) * α ^ (2 * j)) * mainBetaOld) := hWsum.mul_right mainBetaOld
    have hterm (j : ℕ) :
        ((1 - α ^ 2) * α ^ (2 * j)) * mainBetaOld ≤
          ((1 - α ^ 2) * α ^ (2 * j)) * C j ω :=
      mul_le_mul_of_nonneg_left (hCminor j ω)
        (mul_nonneg (sub_nonneg.mpr (pow_le_one₀
          Scalar.inverse_history_discount_range.1.le
          Scalar.inverse_history_discount_range.2.le))
          (pow_nonneg Scalar.inverse_history_discount_range.1.le _))
    have hsum := hbaseSum.tsum_le_tsum hterm (hWcoeffSum ω)
    have hbaseValue : ∑' j : ℕ,
        ((1 - α ^ 2) * α ^ (2 * j)) * mainBetaOld = mainBetaOld := by
      calc
        _ = mainBetaOld * ∑' j : ℕ, (1 - α ^ 2) * α ^ (2 * j) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro j
          ring
        _ = mainBetaOld := by rw [hWtotal]; ring
    rw [hbaseValue] at hsum
    exact hsum
  have hmassEq (ω : CutoffSample 2) :
      (∑' j : ℕ, ((1 - α ^ 2) * α ^ (2 * j)) * C j ω) =
        (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * C j ω := by
    calc
      _ = ∑' j : ℕ, (1 - α ^ 2) * (α ^ (2 * j) * C j ω) := by
        apply tsum_congr
        intro j
        ring
      _ = _ := tsum_mul_left
  have hthetaEq (ω : CutoffSample 2) :
      mixedOldTheta M m U t ω =
        rawWeakTraceProxy (fun j => C j ω) (fun j => T j ω) := by
    unfold mixedOldTheta rawWeakTraceProxy
    calc
      _ = ∑' j : ℕ, (1 - α ^ 2) *
          (α ^ (2 * j) * C j ω * T j ω) := by
        apply tsum_congr
        intro j
        simp [mixedOldThetaTerm, mixedDepthTraceAverage, C, T]
        ring
      _ = _ := tsum_mul_left
  have hgap0 (j : ℕ) (ω : CutoffSample 2) :
      0 ≤ T j ω - rawCubeFourLoadTrace M m U t ω := by
    have hparent := old_signed_parent_trace_le_child U j M.nu σ M.nu_pos hσ (k ω)
    have hparent' : rawCubeFourLoadTrace M m U t ω ≤ T j ω := by
      rw [← hparentTrace ω, ← htrace ω j]
      exact hparent
    exact sub_nonneg.mpr hparent'
  have hgapLeT (j : ℕ) (ω : CutoffSample 2) :
      T j ω - rawCubeFourLoadTrace M m U t ω ≤ T j ω := by
    exact sub_le_self _ (raw_cube_four_load_trace_nonneg M m U t
      ⟨ht.1, ht.2⟩ ω)
  have hdepthRaw : ∀ᵐ ω ∂μ, ∀ j : ℕ, D j ω ≤ C j ω := hdepthAll
  filter_upwards [hdepthRaw] with ω hD
  have hT0 (j : ℕ) : 0 ≤ T j ω := by
    exact raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j
  have hgapSeries : Summable (fun j : ℕ =>
      α ^ (2 * j) * C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω)) := by
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (mul_nonneg (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
        (hCnonneg j ω)) (hgap0 j ω)
    · intro j
      have hterm : C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) ≤ C j ω * T j ω :=
        mul_le_mul_of_nonneg_left (hgapLeT j ω) (hCnonneg j ω)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterm
        (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
    · exact hθSumRight ω
  have hgapSeriesRight : Summable (fun j : ℕ =>
      α ^ (2 * j) * (C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω))) := by
    simpa only [← mul_assoc] using hgapSeries
  have hgapProxyCompare :
      rawWeakTraceProxy (fun j => D j ω)
        (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) ≤
      rawWeakTraceProxy (fun j => C j ω)
        (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) := by
    unfold rawWeakTraceProxy
    apply mul_le_mul_of_nonneg_left _
      (sub_nonneg.mpr (pow_le_one₀ Scalar.inverse_history_discount_range.1.le
        Scalar.inverse_history_discount_range.2.le))
    have hDgapSeries : Summable (fun j : ℕ =>
        α ^ (2 * j) * D j ω *
          (T j ω - rawCubeFourLoadTrace M m U t ω)) := by
      apply Summable.of_nonneg_of_le
      · intro j
        exact mul_nonneg (mul_nonneg
          (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
          (lemmaVInverseDepthMax_nonneg U (a ω) j))
          (hgap0 j ω)
      · intro j
        have hterm : D j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) ≤
            C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) :=
          mul_le_mul_of_nonneg_right (hD j) (hgap0 j ω)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterm
          (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
      · simpa only [mul_assoc] using hgapSeries
    have hterm (j : ℕ) : α ^ (2 * j) * D j ω *
        (T j ω - rawCubeFourLoadTrace M m U t ω) ≤
          α ^ (2 * j) * C j ω *
            (T j ω - rawCubeFourLoadTrace M m U t ω) := by
      have hterm : D j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) ≤
          C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) :=
        mul_le_mul_of_nonneg_right (hD j) (hgap0 j ω)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterm
        (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
    exact hDgapSeries.tsum_le_tsum hterm hgapSeries
  have hpairSeries : Summable (fun j : ℕ => α ^ (2 * j) * D j ω * T j ω) := by
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (mul_nonneg (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
        (lemmaVInverseDepthMax_nonneg U (a ω) j)) (hT0 j)
    · intro j
      simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hD j) (hT0 j))
        (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
    · exact hθSum ω
  have hpairProxyCompare :
      rawWeakTraceProxy (fun j => D j ω) (fun j => T j ω) ≤
      rawWeakTraceProxy (fun j => C j ω) (fun j => T j ω) := by
    unfold rawWeakTraceProxy
    apply mul_le_mul_of_nonneg_left _
      (sub_nonneg.mpr (pow_le_one₀ Scalar.inverse_history_discount_range.1.le
        Scalar.inverse_history_discount_range.2.le))
    have hterm (j : ℕ) : α ^ (2 * j) * D j ω * T j ω ≤
        α ^ (2 * j) * C j ω * T j ω := by
      simpa only [← mul_assoc] using
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hD j) (hT0 j))
          (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
    exact hpairSeries.tsum_le_tsum hterm (hθSum ω)
  have hcoefLower := hmassLower ω
  have hgapMassEq :
      rawWeakTraceProxy (fun j => C j ω)
        (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) =
      mixedOldTheta M m U t ω - rawCubeFourLoadTrace M m U t ω *
        (∑' j : ℕ, ((1 - α ^ 2) * α ^ (2 * j)) * C j ω) := by
    have hCoeffTimesF := (hCoeffSum ω).mul_left
      (rawCubeFourLoadTrace M m U t ω)
    have hsumGap :
        (∑' j : ℕ, α ^ (2 * j) * C j ω *
          (T j ω - rawCubeFourLoadTrace M m U t ω)) =
          (∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
            rawCubeFourLoadTrace M m U t ω *
              (∑' j : ℕ, α ^ (2 * j) * C j ω) := by
      calc
        _ = ∑' j : ℕ,
            (α ^ (2 * j) * C j ω * T j ω -
              rawCubeFourLoadTrace M m U t ω * (α ^ (2 * j) * C j ω)) := by
          apply tsum_congr
          intro j
          ring
        _ = (∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
            (∑' j : ℕ, rawCubeFourLoadTrace M m U t ω *
              (α ^ (2 * j) * C j ω)) := (hθSum ω).tsum_sub hCoeffTimesF
        _ = (∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
            rawCubeFourLoadTrace M m U t ω *
              (∑' j : ℕ, α ^ (2 * j) * C j ω) := by
          rw [tsum_mul_left]
    calc
      _ = (1 - α ^ 2) *
          (∑' j : ℕ, α ^ (2 * j) * C j ω *
            (T j ω - rawCubeFourLoadTrace M m U t ω)) := by
        rfl
      _ = (1 - α ^ 2) *
          ((∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
            rawCubeFourLoadTrace M m U t ω *
              (∑' j : ℕ, α ^ (2 * j) * C j ω)) := by rw [hsumGap]
      _ = (1 - α ^ 2) *
          (∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
          rawCubeFourLoadTrace M m U t ω *
            ((1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * C j ω) := by ring
      _ = mixedOldTheta M m U t ω - rawCubeFourLoadTrace M m U t ω *
          (∑' j : ℕ, ((1 - α ^ 2) * α ^ (2 * j)) * C j ω) := by
        have hthetaValue : mixedOldTheta M m U t ω =
            (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω := by
          simpa [rawWeakTraceProxy] using hthetaEq ω
        rw [← hthetaValue, ← hmassEq ω]
  have hVgap := mixed_bridge_local_primal_gap_proxy' U M.nu σ M.nu_pos hσ (k ω)
  have hVpair := mixed_bridge_local_paired_proxy' U M.nu σ M.nu_pos hσ (k ω)
  constructor
  · calc
      mixedBridgeVLocal M m U t ω ^ 2 ≤
          rawWeakTraceProxy (fun j => D j ω)
            (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) := by
              simpa only [mixedBridgeVLocal, D, T, a, k, σ,
                htrace ω, hparentTrace ω] using hVgap
      _ ≤ rawWeakTraceProxy (fun j => C j ω)
            (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) := hgapProxyCompare
      _ ≤ mixedOldTheta M m U t ω - mainBetaOld *
            rawCubeFourLoadTrace M m U t ω := by
        rw [hgapMassEq]
        have hmass := mul_le_mul_of_nonneg_right hcoefLower
          (raw_cube_four_load_trace_nonneg M m U t ⟨ht.1, ht.2⟩ ω)
        nlinarith [hmass]
  · calc
      mixedBridgeVLocal M m U t ω ^ 2 + mixedBridgeGLocal M m U t ω ^ 2 ≤
          2 * rawWeakTraceProxy (fun j => D j ω) (fun j => T j ω) := by
            simpa only [mixedBridgeVLocal, mixedBridgeGLocal, D, T, a, k, σ,
              htrace ω] using hVpair
      _ ≤ 2 * rawWeakTraceProxy (fun j => C j ω) (fun j => T j ω) :=
        mul_le_mul_of_nonneg_left hpairProxyCompare (by norm_num)
      _ = 2 * mixedOldTheta M m U t ω := by rw [hthetaEq ω]

/-- Local parent-gap rows on each depth-five source cell.  The OLD frame stays
at the insertion label `m`; the inverse envelope is the explicit `mainChi`
envelope, and the local first-corrector carrier is its actual zero series. -/
theorem mixed_bridge_local_parent_gap_rows''
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hscale : U.scale = m - ((5 : ℕ) : ℤ))
    (hUObserver : U ∈ bankObserverRoots (originCube 2 (m + 40)) 5) :
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
        mainEnvelopeH (theta M) M.gamma t := by
  classical
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let v := (q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2
  let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
  let B : Cutoff.CutoffSample 2 → ℝ := mixedGlobalHistoryMax M m t
  let V : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVLocal M m U t
  let G : Cutoff.CutoffSample 2 → ℝ := mixedBridgeGLocal M m U t
  let Vl : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVlLocal M m U t
  let f_U := ∫ ω, rawCubeFourLoadTrace M m U t ω ∂μ

  have hEnvelope := main_envelope_xi_depth5_actual_law'
    M h hM hγ N hpast m hm t ht U hscale
  have hThetaInt : Integrable (mixedOldTheta M m U t) μ := by
    simpa [μ] using (hEnvelope ⟨0, by norm_num⟩).1
  have hBcarrier (ω : Cutoff.CutoffSample 2) :
      B ω = mixedBridgeBstar M m t ω := by
    dsimp [B, mixedGlobalHistoryMax, mixedObserverRoots,
      mixedBridgeBstar]
    rw [← mixed_bridge_observer_roots_eq_bank_union m,
      ← mixed_bridge_bstar_eq_bank_finite_history M m t ht ω]
    exact ENNReal.toReal_ofReal
      (mixed_bridge_bstar_nonneg M m t ω)
  have hBmeas : Measurable B := by
    have heq : B = mixedBridgeBstar M m t := funext hBcarrier
    rw [heq]
    exact parent_gap_bstar_measurable M m t
  have hBnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω := by
    rw [hBcarrier ω]
    exact mixed_bridge_bstar_nonneg M m t ω
  have hVmeas : Measurable (fun ω => V ω ^ 2) := by
    simpa [V] using mixed_bridge_local_v2_measurable' M m U t
  have hGmeas : Measurable (fun ω => G ω ^ 2) := by
    simpa [G] using mixed_bridge_local_measurable' M m U t
  have hThetaNonneg (ω : Cutoff.CutoffSample 2) :
      0 ≤ mixedOldTheta M m U t ω := by
    unfold mixedOldTheta
    apply tsum_nonneg
    intro j
    rw [mixedOldThetaTerm]
    have hcoeff : 0 ≤ mixedOldDepthCoefficient M m t j ω := by
      rw [mixed_old_depth_coefficient_formula]
      change 0 ≤ (3683 / 2500 : ℝ) * (3 : ℝ) ^
        (2 * M.gamma * (j : ℝ)) + positiveSplitRemainder _ _ _
      exact add_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by norm_num) _)) ((positive_split _ _ _).1)
    have hw : 0 ≤ (1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j) :=
      mul_nonneg
        (sub_nonneg.mpr (pow_le_one₀
          Scalar.inverse_history_discount_range.1.le
          Scalar.inverse_history_discount_range.2.le))
        (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
    exact mul_nonneg (mul_nonneg hw hcoeff)
      (raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j)
  have hXiNonneg : 0 ≤ xi := by
    have hpre : 0 ≤ mainSourceInversePrefix := by
      have hbeta : 0 < mainBetaOld / 100 := by norm_num [mainBetaOld]
      exact le_of_lt (lt_trans hbeta mainSourceInversePrefix_gate)
    exact hpre.trans (mainEnvelopeXi_ge_initial (sq_nonneg _)
      M.shellPrefix.gamma_pos.le hγ (ASDExplicitGamma.Cold.cold_theta_pos M).le ht.1)

  have hrows : ∀ᵐ ω ∂μ,
      V ω ^ 2 ≤ mixedOldTheta M m U t ω -
          mainBetaOld * rawCubeFourLoadTrace M m U t ω ∧
      V ω ^ 2 + G ω ^ 2 ≤ 2 * mixedOldTheta M m U t ω := by
    simpa [V, G, μ] using
      mixed_bridge_local_pointwise_rows' M h hM hγ N hpast m hm t ht U hUObserver
  have hTraceLaw := mixed_bridge_local_trace_mean'
    M h hM hγ N hpast m hm t ht 5 le_rfl U hscale 0
  have hTraceInt : Integrable (rawCubeFourLoadTrace M m U t) μ := by
    have hTInt := hTraceLaw.1
    have hEq (ω : Cutoff.CutoffSample 2) :
        mixedDepthTraceAverage M m U t ω 0 =
          rawCubeFourLoadTrace M m U t ω := by
      change Cold.squareCellMean U 0
        (fun C => rawCubeFourLoadTrace M m C.1 t ω) = _
      rw [mixed_bridge_local_squareCellMean_eq_descendantsAverage' U 0
        (fun V => rawCubeFourLoadTrace M m V t ω)]
      simp [descendantsAverage, Homogenization.descendantsAtDepth_zero]
    exact hTInt.congr (Filter.Eventually.of_forall hEq)
  have hGapInt : Integrable
      (fun ω => mixedOldTheta M m U t ω -
        mainBetaOld * rawCubeFourLoadTrace M m U t ω) μ :=
    hThetaInt.sub (hTraceInt.const_mul mainBetaOld)
  have hVInt : Integrable (fun ω => V ω ^ 2) μ := by
    apply hGapInt.mono' hVmeas.aestronglyMeasurable
    filter_upwards [hrows] with ω hω
    have hleft : 0 ≤ V ω ^ 2 := sq_nonneg _
    have hright : 0 ≤ mixedOldTheta M m U t ω -
        mainBetaOld * rawCubeFourLoadTrace M m U t ω := le_trans hleft hω.1
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hω.1
  have hVIntegralBound :
      (∫ ω, V ω ^ 2 ∂μ) ≤ xi - mainBetaOld * f_U := by
    have hmono := integral_mono_ae hVInt hGapInt (by
      filter_upwards [hrows] with ω hω
      exact hω.1)
    have hthetaBound :
        (∫ ω, mixedOldTheta M m U t ω ∂μ) ≤ xi := by
      simpa [μ, xi, v] using (hEnvelope ⟨0, by norm_num⟩).2
    have hgapIntegral :
        (∫ ω, mixedOldTheta M m U t ω -
          mainBetaOld * rawCubeFourLoadTrace M m U t ω ∂μ) ≤
          xi - mainBetaOld * f_U := by
      rw [integral_sub hThetaInt (hTraceInt.const_mul mainBetaOld),
        integral_const_mul]
      exact sub_le_sub_right hthetaBound (mainBetaOld * f_U)
    exact hmono.trans hgapIntegral

  have hPairRows : ∀ k : Fin 4,
      Integrable (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ ∧
      (∫ ω, B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ∂μ) ≤
        2 * mainBeta ^ k.val * xi := by
    intro k
    have hEnv := hEnvelope k
    have hIntegrandMeas : Measurable
        (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) :=
      (hBmeas.pow_const k.val).mul (hVmeas.add hGmeas)
    have hpairInt : Integrable
        (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ := by
      apply (hEnv.1.const_mul 2).mono' hIntegrandMeas.aestronglyMeasurable
      filter_upwards [hrows] with ω hω
      have hpow : 0 ≤ B ω ^ k.val := pow_nonneg (hBnonneg ω) _
      have hleft : 0 ≤ B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) :=
        mul_nonneg hpow (add_nonneg (sq_nonneg _) (sq_nonneg _))
      have hright : 0 ≤ 2 * (B ω ^ k.val * mixedOldTheta M m U t ω) :=
        mul_nonneg (by norm_num) (mul_nonneg hpow (hThetaNonneg ω))
      have hbound : B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ≤
          2 * (B ω ^ k.val * mixedOldTheta M m U t ω) := by
        calc
          _ ≤ B ω ^ k.val * (2 * mixedOldTheta M m U t ω) :=
            mul_le_mul_of_nonneg_left hω.2 hpow
          _ = _ := by ring
      rw [Real.norm_of_nonneg hleft]
      simpa [B] using hbound
    have hpairIntegral := integral_mono_ae hpairInt (hEnv.1.const_mul 2) (by
      filter_upwards [hrows] with ω hω
      have hpow : 0 ≤ B ω ^ k.val := pow_nonneg (hBnonneg ω) _
      calc
        B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ≤
            2 * (B ω ^ k.val * mixedOldTheta M m U t ω) := by
              calc
                _ ≤ B ω ^ k.val * (2 * mixedOldTheta M m U t ω) :=
                  mul_le_mul_of_nonneg_left hω.2 hpow
                _ = _ := by ring
        _ = 2 * (B ω ^ k.val * mixedOldTheta M m U t ω) := rfl)
    have hEnvBound :
        (∫ ω, B ω ^ k.val * mixedOldTheta M m U t ω ∂μ) ≤
          mainBeta ^ k.val * xi := by
      simpa [B, μ, xi, v] using hEnv.2
    refine ⟨hpairInt, ?_⟩
    calc
      _ ≤ 2 * (∫ ω, B ω ^ k.val * mixedOldTheta M m U t ω ∂μ) := by
        simpa only [integral_const_mul] using hpairIntegral
      _ ≤ 2 * (mainBeta ^ k.val * xi) :=
        mul_le_mul_of_nonneg_left hEnvBound (by norm_num)
      _ = 2 * mainBeta ^ k.val * xi := by ring

  have hGInt : Integrable (fun ω => B ω * G ω ^ 2) μ := by
    have hmeas : Measurable (fun ω => B ω * G ω ^ 2) := hBmeas.mul hGmeas
    have hpair := hPairRows ⟨1, by norm_num⟩ |>.1
    apply hpair.mono' hmeas.aestronglyMeasurable
    filter_upwards with ω
    have hleft : 0 ≤ B ω * G ω ^ 2 := mul_nonneg (hBnonneg ω) (sq_nonneg _)
    have hright : 0 ≤ B ω ^ 1 * (V ω ^ 2 + G ω ^ 2) :=
      mul_nonneg (pow_nonneg (hBnonneg ω) 1)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hbound : B ω * G ω ^ 2 ≤ B ω ^ 1 * (V ω ^ 2 + G ω ^ 2) := by
      have hbase : G ω ^ 2 ≤ V ω ^ 2 + G ω ^ 2 := by nlinarith [sq_nonneg (V ω)]
      simpa only [pow_one] using mul_le_mul_of_nonneg_left hbase (hBnonneg ω)
    rw [Real.norm_of_nonneg hleft]
    simpa only [pow_one] using hbound
  have hGIntegralBound :
      (∫ ω, B ω * G ω ^ 2 ∂μ) ≤ 2 * mainBeta * xi := by
    have hmono := integral_mono_ae hGInt
      (hPairRows ⟨1, by norm_num⟩).1 (by
        filter_upwards with ω
        have hbase : G ω ^ 2 ≤ V ω ^ 2 + G ω ^ 2 := by nlinarith [sq_nonneg (V ω)]
        simpa only [pow_one] using mul_le_mul_of_nonneg_left hbase (hBnonneg ω))
    have hpairBound := (hPairRows ⟨1, by norm_num⟩).2
    simpa only [pow_one] using hmono.trans hpairBound

  have hVlZero (ω : CutoffSample 2) : Vl ω ^ 2 = 0 := by
    simp [Vl, mixedBridgeVlLocal, mixed_bridge_local_vl2_zero']
  have hVlInt : Integrable (fun ω => B ω * Vl ω ^ 2) μ := by
    have heq : (fun ω => B ω * Vl ω ^ 2) = fun _ : CutoffSample 2 => 0 := by
      funext ω
      rw [hVlZero ω]
      ring
    rw [heq]
    exact integrable_const 0
  have hVlIntegral : (∫ ω, B ω * Vl ω ^ 2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with ω
    simp [hVlZero ω]
  have hVlBound :
      (∫ ω, B ω * Vl ω ^ 2 ∂μ) ≤
        mainBeta * xi + mainEpsNew * mainD * mainBeta *
          mainEnvelopeH (theta M) M.gamma t := by
    rw [hVlIntegral]
    have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
    have hε : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
    have hAlpha : 0 ≤ mainAlpha :=
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
    have hD : 0 ≤ mainD := by
      dsimp [mainD]
      exact add_nonneg (by norm_num) hAlpha
    have hH : 0 ≤ mainEnvelopeH (theta M) M.gamma t :=
      mainEnvelopeH_nonneg _ _ _
    positivity

  refine ⟨hVInt, hVIntegralBound, hPairRows, hGInt, hGIntegralBound,
    hVlInt, hVlBound⟩

end

end ASDExplicitGamma.Main
