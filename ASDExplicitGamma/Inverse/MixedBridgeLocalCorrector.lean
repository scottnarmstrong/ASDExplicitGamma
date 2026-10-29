module

public import ASDExplicitGamma.Inverse.BridgeObservables
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Native.OldSignedCellPotentials
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Scalar.LocalProjectionOrthogonality
public import ASDExplicitGamma.Triadic.DiagEnergyCongr

/-! The actual local corrector of a parent canonical minimizer vanishes.
The child coefficient is the restriction of the parent coefficient, and
zero-trace child variations extend to admissible parent variations. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Response Scalar Triadic Variational
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Native ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 ASDExplicitGamma.Cold
open scoped BigOperators RealInnerProductSpace

noncomputable section

private theorem mixed_bridge_parent_canonical_cell_residual_eq
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

/-- The actual first-corrector gradient of each local restriction of the
parent canonical minimizer is zero almost everywhere on the child. -/
theorem mixed_bridge_local_corrector_grad_zero
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (j : ℕ) (C : SquareCells (originCube 2 m) j) (a : BlockCoord 2) :
    let Q := originCube 2 m
    let U := C.val
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth C.property
    let k := mixedBridgeResponseCoefficient m t ω
    let sigma : ℝ := Annealed.sigmaBar M m
    let hsigma : 0 < sigma := (Annealed.sigmaBar_characterization M m).1
    let F := oldSignedFrameCanonicalField Q M.nu sigma M.nu_pos hsigma k (blockBasis a)
    let hF : MemBlockL2 (openCubeSet Q) F := Lp.memLp F
    (oldSignedCellFirstCorrector Q U hU M.nu sigma M.nu_pos hsigma k F hF).toH1Function.grad =ᵐ[
      volumeMeasureOn (openCubeSet U)] 0 := by
  dsimp only
  let Q := originCube 2 m
  let U := C.val
  let hU := openCubeSet_subset_of_mem_descendantsAtDepth C.property
  let k := mixedBridgeResponseCoefficient m t ω
  let sigma : ℝ := Annealed.sigmaBar M m
  let hsigma : 0 < sigma := (Annealed.sigmaBar_characterization M m).1
  let F := oldSignedFrameCanonicalField Q M.nu sigma M.nu_pos hsigma k (blockBasis a)
  let hF : MemBlockL2 (openCubeSet Q) F := Lp.memLp F
  rw [old_signed_cell_first_corrector_grad]
  have hres := mixed_bridge_parent_canonical_cell_residual_eq
    Q U hU M.nu sigma M.nu_pos hsigma k (blockBasis a)
  filter_upwards [hres] with x hx
  have hfirst :
      (oldSignedCellResidual Q U hU M.nu sigma M.nu_pos hsigma k F hF x).1 = (F x).1 :=
    congrArg Prod.fst hx
  change (oldSignedCellResidual Q U hU M.nu sigma M.nu_pos hsigma k F hF x).1 - (F x).1 = 0
  exact sub_eq_zero.mpr hfirst

private theorem vectorWeakHaarNorm_zero_of_ae_eq_zero
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
  rw [show vectorWeakHaarEnergy Q F = vectorWeakHaarEnergy Q 0 by
    unfold vectorWeakHaarEnergy
    apply Finset.sum_congr rfl
    intro i hi
    unfold dualEnergy
    exact diagPrimalEnergy_congr_ae Q (Real.sqrt 3)⁻¹ (hcoord i)]
  simp [vectorWeakHaarEnergy, dualEnergy, primalEnergy, energy, pairing,
    cubeIncrement_zero, cubeIncrement_succ, hzeroProj, cubeAverage_const]

/-- The pointwise local first-corrector square in `V_l²` vanishes for the
actual parent canonical fields used by the mixed-bridge carrier. -/
theorem mixed_bridge_local_corrector_square_zero
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (j : ℕ) (C : SquareCells (originCube 2 m) j) :
    mixedBridgeLocalCorrectorSq M m t ω j C = 0 := by
  classical
  unfold mixedBridgeLocalCorrectorSq
  apply Finset.sum_eq_zero
  intro a ha
  have hgrad := mixed_bridge_local_corrector_grad_zero M m t ω j C a
  rw [vectorWeakHaarNorm_zero_of_ae_eq_zero C.val hgrad]
  simp

/-- Every finite local depth average in the actual `V_l²` carrier is zero. -/
theorem mixed_bridge_vlocal_depth_square_zero
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    mixedBridgeVLocalDepthSq M m t ω j = 0 := by
  classical
  unfold mixedBridgeVLocalDepthSq ASDExplicitGamma.Cold.squareCellMean
  have hsum : ∑ C : SquareCells (originCube 2 m) j,
      mixedBridgeLocalCorrectorSq M m t ω j C = 0 := by
    apply Finset.sum_eq_zero
    intro C hC
    exact mixed_bridge_local_corrector_square_zero M m t ω j C
  rw [hsum]
  simp

/-- The actual source carrier `V_l²` is identically zero for the parent
canonical minimizers used in `IN-MIXED-BRIDGE`. -/
theorem mixed_bridge_vl2_zero
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    mixedBridgeVl2 M m t ω = 0 := by
  unfold mixedBridgeVl2
  have hz (j : ℕ) : mixedBridgeVLocalDepthSq M m t ω j = 0 :=
    mixed_bridge_vlocal_depth_square_zero M m t ω j
  simp_rw [hz]
  simp

end

end ASDExplicitGamma.Inverse
