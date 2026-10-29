module

public import ASDExplicitGamma.Inverse.BridgeObservables
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTrace
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Native.OldSignedCellPotentials
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Scalar.LocalProjectionOrthogonality
public import ASDExplicitGamma.Triadic.DiagEnergyCongr

/-! The actual mixed-bridge carriers on an arbitrary source cell, with the
insertion shell and OLD frame fixed at the completed scale. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Response Scalar Triadic Variational
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Native ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 ASDExplicitGamma.Cold
open scoped BigOperators RealInnerProductSpace
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

local instance mixedBridgeDepthZeroCellsUnique (Q : TriadicCube 2) :
    Unique (SquareCells Q 0) where
  default := ⟨Q, by simp [Homogenization.descendantsAtDepth_zero]⟩
  uniq C := by
    apply Subtype.ext
    simpa [Homogenization.descendantsAtDepth_zero] using C.property

/-- The actual partial-insertion coefficient restricted to an arbitrary
triadic cube. -/
noncomputable def mixedBridgeResponseCoefficientOnCube (Q : TriadicCube 2)
    (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    ResponseCoefficient (openCubeSet Q) := by
  let K := closure (cubeSet Q)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (isBounded_cubeSet Q).isCompact_closure
  exact ASDExplicitGamma.Main.mainAffineOpenResponseRestriction Q
    (modelInsertedScalar K m t ω)

/-- The actual local four-load primal error square rooted at the source cell.
The partial coefficient and true OLD frame use `m`, even though `U.scale=m-5`.
-/
noncomputable def mixedBridgeSourceCellV2 (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let sigma : ℝ := Annealed.sigmaBar M m
  oldSignedPrimalErrorSize U U M.nu sigma M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (mixedBridgeResponseCoefficientOnCube U m t ω) ^ 2

/-- The local primal source size. -/
noncomputable def mixedBridgeSourceCellV (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt (mixedBridgeSourceCellV2 M m U t ω)

/-- Remove the nonnegative square-root presentation of the local primal
carrier; this is the same actual parent error size. -/
theorem mixedBridgeSourceCellV_eq_primal_error_size
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    mixedBridgeSourceCellV M m U t ω =
      oldSignedPrimalErrorSize U U M.nu (Annealed.sigmaBar M m) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mixedBridgeResponseCoefficientOnCube U m t ω) := by
  unfold mixedBridgeSourceCellV mixedBridgeSourceCellV2
  rw [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (show 0 ≤ oldSignedPrimalErrorSize U U M.nu
      (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1
      (mixedBridgeResponseCoefficientOnCube U m t ω) from by
        unfold oldSignedPrimalErrorSize
        positivity)]

/-- The actual local four-load reciprocal error square rooted at the source
cell, with the same partial coefficient and true OLD frame. -/
noncomputable def mixedBridgeSourceCell (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let sigma : ℝ := Annealed.sigmaBar M m
  oldSignedReciprocalErrorSize U U M.nu sigma M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (mixedBridgeResponseCoefficientOnCube U m t ω) ^ 2

/-- The local reciprocal source size. -/
noncomputable def mixedBridgeSourceCellG (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt (mixedBridgeSourceCell M m U t ω)

/-- Remove the nonnegative square-root presentation of the local reciprocal
carrier; this is the same actual parent error size. -/
theorem mixedBridgeSourceCellG_eq_reciprocal_error_size
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    mixedBridgeSourceCellG M m U t ω =
      oldSignedReciprocalErrorSize U U M.nu (Annealed.sigmaBar M m) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mixedBridgeResponseCoefficientOnCube U m t ω) := by
  unfold mixedBridgeSourceCellG mixedBridgeSourceCell
  rw [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (show 0 ≤ oldSignedReciprocalErrorSize U U M.nu
      (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1
      (mixedBridgeResponseCoefficientOnCube U m t ω) from by
        unfold oldSignedReciprocalErrorSize
        positivity)]

/-- The actual local first-corrector square on one depth-`j` descendant,
using the canonical minimizers on its source-cell parent `U`. -/
noncomputable def mixedBridgeSourceCellCorrectorSq (M : ABKModel 2)
    (m : ℤ) (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (j : ℕ) (C : SquareCells U j) : ℝ := by
  let W := C.val
  let hW : openCubeSet W ⊆ openCubeSet U :=
    openCubeSet_subset_of_mem_descendantsAtDepth C.property
  let k := mixedBridgeResponseCoefficientOnCube U m t ω
  let sigma : ℝ := Annealed.sigmaBar M m
  let hsigma : 0 < sigma := (Annealed.sigmaBar_characterization M m).1
  exact ∑ a : BlockCoord 2,
    vectorWeakHaarNorm W (fun x =>
      (oldSignedCellFirstCorrector U W hW M.nu sigma M.nu_pos hsigma k
        (oldSignedFrameCanonicalField U M.nu sigma M.nu_pos hsigma k (blockBasis a))
        (Lp.memLp (oldSignedFrameCanonicalField U M.nu sigma M.nu_pos hsigma k
          (blockBasis a)))).toH1Function.grad x) ^ 2

/-- Average the actual local corrector squares over the complete local
depth-`j` tiling. -/
noncomputable def mixedBridgeSourceCellVLocalDepthSq (M : ABKModel 2)
    (m : ℤ) (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (j : ℕ) : ℝ :=
  squareCellMean U j (mixedBridgeSourceCellCorrectorSq M m U t ω j)

/-- The complete discounted local weak-corrector energy. -/
noncomputable def mixedBridgeSourceCellVl2 (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' j : ℕ,
    (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
      mixedBridgeSourceCellVLocalDepthSq M m U t ω j

/-- The source local first-corrector size `V_l,U`. -/
noncomputable def mixedBridgeSourceCellVl (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt (mixedBridgeSourceCellVl2 M m U t ω)

/-- The local trace in the gap row is the actual shifted source mean at row
five. -/
theorem mixed_bridge_source_cell_trace_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 m) 5) :
    Integrable (fun ω => rawWeakTraceSequence M m U t ω 0)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, rawWeakTraceSequence M m U t ω 0
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = inSourceMeanActual M m 5 t := by
  have hmean := mixed_bridge_local_trace_mean M h hM hγ N hpast m hm t ht
    5 (by omega) U hU 0
  simpa only [mixedDepthTraceAverage] using hmean

/-- At local depth zero, the weak trace average is exactly the single-cell
four-load trace. -/
theorem rawWeakTraceSequence_zero_eq_rawCubeFourLoadTrace
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    rawWeakTraceSequence M m U t ω 0 = rawCubeFourLoadTrace M m U t ω := by
  have hdefault : (default : SquareCells U 0).val = U := by
    change (mixedBridgeDepthZeroCellsUnique U).default.val = U
    rfl
  simp [rawWeakTraceSequence, squareCellMean,
    Homogenization.descendantsAtDepth_zero, hdefault]

/-- The local gap-row trace is the actual raw four-load trace on `U`, with
the expected shifted source mean at row five. -/
theorem mixed_bridge_source_cell_raw_trace_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 m) 5) :
    Integrable (fun ω => rawCubeFourLoadTrace M m U t ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, rawCubeFourLoadTrace M m U t ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = inSourceMeanActual M m 5 t := by
  simpa only [rawWeakTraceSequence_zero_eq_rawCubeFourLoadTrace] using
    mixed_bridge_source_cell_trace_mean M h hM hγ N hpast m hm t ht U hU

/-- Restricting the true parent canonical minimizer to a child preserves the
minimizer: the child's coefficient is the exact restriction of the parent
coefficient, and every zero-trace child variation is admissible on the parent.
-/
theorem mixed_bridge_parent_canonical_cell_residual_eq'
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
              (responseFramePlanarCoefficientField nu sigma kU) x)
              (F x))) =
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

/-- The first-corrector gradient vanishes when the source is the actual
canonical minimizer on its parent cell. -/
theorem mixed_bridge_parent_canonical_corrector_grad_zero
    (M : ABKModel 2) (m : ℤ) (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (P : BlockVec 2) :
    let k := mixedBridgeResponseCoefficientOnCube Q m t ω
    let sigma : ℝ := Annealed.sigmaBar M m
    let hsigma : 0 < sigma := (Annealed.sigmaBar_characterization M m).1
    let F := oldSignedFrameCanonicalField Q M.nu sigma M.nu_pos hsigma k P
    let hF : MemBlockL2 (openCubeSet Q) F := Lp.memLp F
    (oldSignedCellFirstCorrector Q U hU M.nu sigma M.nu_pos hsigma k F hF).toH1Function.grad =ᵐ[
      volumeMeasureOn (openCubeSet U)] 0 := by
  dsimp only
  let k := mixedBridgeResponseCoefficientOnCube Q m t ω
  let sigma : ℝ := Annealed.sigmaBar M m
  let hsigma : 0 < sigma := (Annealed.sigmaBar_characterization M m).1
  let F := oldSignedFrameCanonicalField Q M.nu sigma M.nu_pos hsigma k P
  let hF : MemBlockL2 (openCubeSet Q) F := Lp.memLp F
  rw [old_signed_cell_first_corrector_grad]
  have hres := mixed_bridge_parent_canonical_cell_residual_eq'
    Q U hU M.nu sigma M.nu_pos hsigma k P
  filter_upwards [hres] with x hx
  have hfirst :
      (oldSignedCellResidual Q U hU M.nu sigma M.nu_pos hsigma k F hF x).1 = (F x).1 :=
    congrArg Prod.fst hx
  change (oldSignedCellResidual Q U hU M.nu sigma M.nu_pos hsigma k F hF x).1 - (F x).1 = 0
  exact sub_eq_zero.mpr hfirst

private theorem mixed_bridge_vector_weak_norm_zero
    (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : F =ᵐ[volumeMeasureOn (openCubeSet Q)] 0) :
    vectorWeakHaarNorm Q F = 0 := by
  have hF' : F =ᵐ[volume.restrict (cubeSet Q)] 0 := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact hF
  have hcoord (i : Fin 2) :
      (fun x => F x i) =ᵐ[volume.restrict (cubeSet Q)] 0 := by
    filter_upwards [hF'] with x hx
    exact congrArg (fun v : Vec 2 => v i) hx
  have hzeroProj (j : ℕ) : cubeProjection Q j (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
    funext x
    simp [cubeProjection, cubeAverage_const]
  unfold vectorWeakHaarNorm
  rw [show vectorWeakHaarEnergy Q F = vectorWeakHaarEnergy Q 0 by
    unfold vectorWeakHaarEnergy
    apply Finset.sum_congr rfl
    intro i hi
    unfold dualEnergy
    exact diagPrimalEnergy_congr_ae Q (Real.sqrt 3)⁻¹ (hcoord i)]
  simp [vectorWeakHaarEnergy, dualEnergy, primalEnergy, energy, pairing,
    cubeIncrement_zero, cubeIncrement_succ, hzeroProj, cubeAverage_const]

/-- Each summand in the source-cell corrector energy vanishes. -/
theorem mixed_bridge_source_cell_corrector_square_zero
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) (C : SquareCells U j) :
    mixedBridgeSourceCellCorrectorSq M m U t ω j C = 0 := by
  classical
  unfold mixedBridgeSourceCellCorrectorSq
  apply Finset.sum_eq_zero
  intro a ha
  have hgrad := mixed_bridge_parent_canonical_corrector_grad_zero
    M m U C.val (openCubeSet_subset_of_mem_descendantsAtDepth C.property) t ω
    (blockBasis a)
  rw [mixed_bridge_vector_weak_norm_zero C.val hgrad]
  simp

/-- Every finite local depth average in the actual source-cell `V_l²`
carrier vanishes. -/
theorem mixed_bridge_source_cell_vlocal_depth_square_zero
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    mixedBridgeSourceCellVLocalDepthSq M m U t ω j = 0 := by
  classical
  unfold mixedBridgeSourceCellVLocalDepthSq ASDExplicitGamma.Cold.squareCellMean
  have hsum : ∑ C : SquareCells U j,
      mixedBridgeSourceCellCorrectorSq M m U t ω j C = 0 := by
    apply Finset.sum_eq_zero
    intro C hC
    exact mixed_bridge_source_cell_corrector_square_zero M m U t ω j C
  rw [hsum]
  simp

/-- The complete local corrector energy is zero for the actual parent
canonical minimizers. -/
theorem mixed_bridge_source_cell_vl2_zero
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    mixedBridgeSourceCellVl2 M m U t ω = 0 := by
  unfold mixedBridgeSourceCellVl2
  have hz (j : ℕ) : mixedBridgeSourceCellVLocalDepthSq M m U t ω j = 0 :=
    mixed_bridge_source_cell_vlocal_depth_square_zero M m U t ω j
  simp_rw [hz]
  simp

/-- The source local first-corrector size vanishes pathwise. -/
theorem mixed_bridge_source_cell_vl_zero
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    mixedBridgeSourceCellVl M m U t ω = 0 := by
  rw [mixedBridgeSourceCellVl,
    mixed_bridge_source_cell_vl2_zero M m U t ω]
  simp

end
end ASDExplicitGamma.Inverse
