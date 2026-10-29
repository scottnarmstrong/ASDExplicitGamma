module

public import ASDExplicitGamma.Cold.NativeResponseLaw
public import ASDExplicitGamma.Cold.NativeSubadditivity
public import ASDExplicitGamma.Cold.CoarseGramDefect
public import ASDExplicitGamma.Scalar.OldCutoffCoefficient
public import ASDExplicitGamma.Scalar.ResidualSourcePairing
public import ASDExplicitGamma.Scalar.CellResponseTest
public import ASDExplicitGamma.Scalar.CutoffProjection
public import ASDExplicitGamma.Triadic.VectorHaar
public import ASDExplicitGamma.Triadic.SensitivityWeakEnergy
public import ASDExplicitGamma.Cold.SquareProjectionAE
public import ASDExplicitGamma.Native.OldSignedAffineReciprocalBounds

/-! The actual cellwise coarse-response carriers used by the smooth
feedback estimate. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open Algsuperdiff.Section3

noncomputable section

private theorem smooth_feedback_response_entry_integrable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (i j : BlockCoord 2) :
    Integrable (fun ω => Cold.coldNativeResponse M m Q ω i j)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hT := Cold.coldNativeCellTrace_integrable M m Q
  have hmajor : Integrable
      (fun ω => Cold.coldNativeCellTrace M m Q ω + 2) μ :=
    hT.add (integrable_const 2)
  have hmeas : Measurable (fun ω => Cold.coldNativeResponse M m Q ω i j) :=
    (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (Cold.coldNativeResponse_measurable M m Q))
  refine hmajor.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  have hTnonneg := Cold.coldNativeCellTrace_nonneg M m Q ω
  have hspec := Cold.coldNativeResponse_spectral M m Q ω
  have hentry := Cold.matrix_entry_abs_le_trace_add_two
    (Cold.coldNativeResponse M m Q ω) hTnonneg hspec i j
  change ‖Cold.coldNativeResponse M m Q ω i j‖ ≤
    Cold.coldNativeCellTrace M m Q ω + 2
  rw [Real.norm_eq_abs]
  exact hentry

/-- The OLD-law response on a cell in the fixed true frame.  This is the
framed CoarseGraining response of the actual cutoff coefficient. -/
def smoothFeedbackCellA (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : BlockMat 2 :=
  Variational.frameMatrix (Annealed.sigmaBar M m : ℝ)
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun)

/-- The affine top block of the actual framed local response. -/
def smoothFeedbackCellK (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : Mat 2 :=
  (smoothFeedbackCellA M m Q ω).upperLeft

/-- The reciprocal lower block of the actual framed local response. -/
def smoothFeedbackCellD (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : Mat 2 :=
  (smoothFeedbackCellA M m Q ω).lowerRight

/-- The trace excess of the actual framed local response, in the same gauge
and frame as the OLD trace input. -/
def smoothFeedbackCellT (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  Cold.coldNativeCellTrace M m Q ω

/-- The same literal OLD skew stream presented on the closed physical cube,
for the public coarse-frame adapter. -/
noncomputable def smoothFeedbackCellCubeCoefficient (m : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    ResponseCoefficient (cubeSet Q) := by
  let K := closure (cubeSet Q)
  letI hK : CompactSpace K :=
    isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Cutoff.cutoff m ω x.1 1 0,
      (Cutoff.continuous_cutoffValue_entry m ω 1 0).comp continuous_subtype_val⟩

/-- The physical planar field of the closed-cube stream is the actual OLD
cutoff coefficient on its domain. -/
theorem smooth_feedback_cube_physical_coefficient
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    responsePlanarCoefficientField M.nu
        (smoothFeedbackCellCubeCoefficient m Q ω) =ᵐ[volume.restrict (cubeSet Q)]
      (Cutoff.coefficientCutoff M.nu m ω).toFun := by
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
  rw [responsePlanarCoefficientField, responseCoefficientExtension_eq
    (smoothFeedbackCellCubeCoefficient m Q ω) hx]
  change responsePlanarCoefficient M.nu (Cutoff.cutoff m ω x 1 0) = _
  exact old_cutoff_coefficient_planar M.nu m ω x

/-- The affine minimizer's coefficient is the literal OLD coefficient in the
true frame, almost everywhere on the open source cell. -/
theorem smooth_feedback_open_frame_coefficients_ae
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m Q ω) =ᵐ[volume.restrict (openCubeSet Q)]
      responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (smoothFeedbackCellCubeCoefficient m Q ω) := by
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  have hright : responseCoefficientExtension
      (smoothFeedbackCellCubeCoefficient m Q ω) x = Cutoff.cutoff m ω x 1 0 := by
    rw [responseCoefficientExtension_eq (smoothFeedbackCellCubeCoefficient m Q ω)
      (openCubeSet_subset_cubeSet Q hx)]
    rfl
  rw [responseFramePlanarCoefficientField_apply, responseFramePlanarCoefficientField_apply,
    hright]
  rw [old_cutoff_skew_coefficient_value m Q ω hx]

/-- The directional diagonal response excess on one actual source cell. -/
def smoothFeedbackPairCharge (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (w : Vec 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w) +
    vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w) - 2 * vecNormSq w

/-- The literal OLD-law affine minimizer of a constant affine-top load on one
source cell. This is the canonical recovered-field representative of
`Q_{a,U}(e,0)` for the normalized actual cutoff coefficient in the true
`sigmaBar` frame. -/
noncomputable def smoothFeedbackCellAffineResidual (M : ABKModel 2)
    (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) : Vec 2 → BlockVec 2 := by
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
    (oldCutoffSkewCoefficient m Q ω)
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
  exact (scalarCellResponseTest Q a hEll (e, 0)).eval

/-- The canonical recovered affine minimizer is the same local field as the
literal weighted projection residual used by the existing source history
estimates. -/
theorem smooth_feedback_affine_projection_ae
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    (fun x => scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
      ((scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)).constantField
        (e, 0)) x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      smoothFeedbackCellAffineResidual M m Q e ω := by
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
    (oldCutoffSkewCoefficient m Q ω)
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
  let S := scalarCellSystem Q a hEll
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hrec := Variational.lemmaV_recovered_minimizer_ae
    (U := openCubeSet Q) (hU := isOpenBoundedConvexDomain_openCubeSet Q)
    (a := a) (hEll := hEll) (hvol := hvol) (e, 0)
  let recovery := Variational.lemmaVRecoveryData
    (isOpenBoundedConvexDomain_openCubeSet Q)
  change hilbertBlockL2ToBlockL2 (S.toMuHilbertRealization.minimizerMap (e, 0)) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
    (fun x => (recovery.toMuCorrectionSpaceRecoveryData.recoveredField S (e, 0)).eval x)
      at hrec
  have hprojection :
      scalarProjectionResidual Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
        ((scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)).constantField
          (e, 0)) = S.toMuHilbertRealization.minimizerMap (e, 0) := by
    rw [scalarProjectionResidual_eq_affineMinimizer]
    rfl
  rw [← hprojection] at hrec
  simpa [scalarResidualField, smoothFeedbackCellAffineResidual,
    scalarCellResponseTest, a, hEll, S, recovery] using hrec

/-- The complementary weighted projection is linear in its Hilbert-space
load. -/
theorem smooth_feedback_scalar_projection_residual_add
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (F G : HilbertBlockL2 (openCubeSet Q)) :
    scalarProjectionResidual Q ν σ hν hσ k (F + G) =
      scalarProjectionResidual Q ν σ hν hσ k F +
        scalarProjectionResidual Q ν σ hν hσ k G := by
  rw [scalarProjectionResidual_eq_affineMinimizer Q ν σ hν hσ k (F + G),
    scalarProjectionResidual_eq_affineMinimizer Q ν σ hν hσ k F,
    scalarProjectionResidual_eq_affineMinimizer Q ν σ hν hσ k G]
  exact (Homogenization.affineMinimizerMap
    (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin
    (scalarFrameRealization Q ν σ hν hσ k).energyCoercive).map_add F G

/-- The actual scalar residual field is additive in its affine load. -/
theorem smooth_feedback_scalar_residual_field_add
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (F G : HilbertBlockL2 (openCubeSet Q)) :
    scalarResidualField Q ν σ hν hσ k (F + G) =
      scalarResidualField Q ν σ hν hσ k F +
        scalarResidualField Q ν σ hν hσ k G := by
  change hilbertBlockL2ToBlockL2
      (scalarProjectionResidual Q ν σ hν hσ k (F + G)) = _
  rw [smooth_feedback_scalar_projection_residual_add]
  exact (hilbertBlockL2ToBlockL2 (U := openCubeSet Q)).map_add _ _

/-- The canonical recovered affine minimizer on the actual OLD cutoff cell
is additive in its constant load, almost everywhere. -/
theorem smooth_feedback_affine_residual_add_ae
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (e f : Vec 2) (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellAffineResidual M m Q (e + f) ω =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => smoothFeedbackCellAffineResidual M m Q e ω x +
        smoothFeedbackCellAffineResidual M m Q f ω x) := by
  let k := oldCutoffSkewCoefficient m Q ω
  let R := scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar M m).property k
  have hload : R.constantField ((e + f, 0) : BlockVec 2) =
      R.constantField (e, 0) + R.constantField (f, 0) := by
    have hpair : ((e + f, 0) : BlockVec 2) = (e, 0) + (f, 0) := by
      ext i <;> fin_cases i <;> simp
    rw [hpair, map_add]
  have hsource : scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField ((e + f, 0))) =
      scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (e, 0)) +
      scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (f, 0)) := by
    calc
      _ = scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k
          (R.constantField (e, 0) + R.constantField (f, 0)) := by rw [hload]
      _ = _ := smooth_feedback_scalar_residual_field_add Q M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property k
        (R.constantField (e, 0)) (R.constantField (f, 0))
  have hsum := smooth_feedback_affine_projection_ae M m Q (e + f) ω
  have he := smooth_feedback_affine_projection_ae M m Q e ω
  have hf := smooth_feedback_affine_projection_ae M m Q f ω
  have hadd := MeasureTheory.Lp.coeFn_add
    (scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (e, 0)))
    (scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (f, 0)))
  filter_upwards [hsum, he, hf, hadd] with x hsum he hf hadd
  calc
    smoothFeedbackCellAffineResidual M m Q (e + f) ω x =
        scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField ((e + f, 0))) x := hsum.symm
    _ = scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (e, 0)) x +
        scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (f, 0)) x := by
      calc
        _ = (scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
            M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (e, 0)) +
            scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
              M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (f, 0))) x :=
          congrArg (fun Z : BlockL2 (openCubeSet Q) => Z x) hsource
        _ = _ := hadd
    _ = smoothFeedbackCellAffineResidual M m Q e ω x +
        smoothFeedbackCellAffineResidual M m Q f ω x := by rw [he, hf]

/-- The complementary weighted projection is homogeneous in its Hilbert-space
load. -/
theorem smooth_feedback_scalar_projection_residual_smul
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (c : ℝ)
    (F : HilbertBlockL2 (openCubeSet Q)) :
    scalarProjectionResidual Q ν σ hν hσ k (c • F) =
      c • scalarProjectionResidual Q ν σ hν hσ k F := by
  rw [scalarProjectionResidual_eq_affineMinimizer Q ν σ hν hσ k (c • F),
    scalarProjectionResidual_eq_affineMinimizer Q ν σ hν hσ k F]
  exact (Homogenization.affineMinimizerMap
    (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin
    (scalarFrameRealization Q ν σ hν hσ k).energyCoercive).map_smul c F

/-- The actual scalar residual field is homogeneous in its affine load. -/
theorem smooth_feedback_scalar_residual_field_smul
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (c : ℝ)
    (F : HilbertBlockL2 (openCubeSet Q)) :
    scalarResidualField Q ν σ hν hσ k (c • F) =
      c • scalarResidualField Q ν σ hν hσ k F := by
  change hilbertBlockL2ToBlockL2
      (scalarProjectionResidual Q ν σ hν hσ k (c • F)) =
    c • hilbertBlockL2ToBlockL2 (scalarProjectionResidual Q ν σ hν hσ k F)
  rw [smooth_feedback_scalar_projection_residual_smul]
  exact (hilbertBlockL2ToBlockL2 (U := openCubeSet Q)).map_smul c
    (scalarProjectionResidual Q ν σ hν hσ k F)

/-- The canonical recovered affine minimizer on the actual OLD cutoff cell
is homogeneous in its constant load, almost everywhere. -/
theorem smooth_feedback_affine_residual_smul_ae
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (c : ℝ) (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellAffineResidual M m Q (c • e) ω =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => c • smoothFeedbackCellAffineResidual M m Q e ω x) := by
  let k := oldCutoffSkewCoefficient m Q ω
  let R := scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar M m).property k
  have hload : R.constantField ((c • e, 0) : BlockVec 2) =
      c • R.constantField (e, 0) := by
    have hpair : ((c • e, 0) : BlockVec 2) = c • (e, 0) := by
      ext i <;> fin_cases i <;> simp
    rw [hpair, map_smul]
  have hsource : scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (c • e, 0)) =
      c • scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (e, 0)) := by
    calc
      _ = scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k
          (c • R.constantField (e, 0)) := by rw [hload]
      _ = _ := smooth_feedback_scalar_residual_field_smul Q M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property k c
        (R.constantField (e, 0))
  have hc := smooth_feedback_affine_projection_ae M m Q (c • e) ω
  have he := smooth_feedback_affine_projection_ae M m Q e ω
  have hscale := MeasureTheory.Lp.coeFn_smul c
    (scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (e, 0)))
  filter_upwards [hc, he, hscale] with x hc he hscale
  calc
    smoothFeedbackCellAffineResidual M m Q (c • e) ω x =
        scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (c • e, 0)) x := hc.symm
    _ = (c • scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (e, 0))) x :=
      congrArg (fun Z : BlockL2 (openCubeSet Q) => Z x) hsource
    _ = c • scalarResidualField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property k (R.constantField (e, 0)) x := hscale
    _ = c • smoothFeedbackCellAffineResidual M m Q e ω x := by rw [he]

/-- The affine-top defect `p_e-e` from the actual local affine minimizer. -/
noncomputable def smoothFeedbackCellAffineTopDefect (M : ABKModel 2)
    (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) : Vec 2 → Vec 2 :=
  fun x => (smoothFeedbackCellAffineResidual M m Q e ω x).1 - e

/-- The reciprocal gradient `g_e` is the lower component of the actual
coefficient image of the affine minimizer `Q_{a,U}(e,0)`. -/
noncomputable def smoothFeedbackCellAffineReciprocalGradient
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) : Vec 2 → Vec 2 :=
  fun x => (scalarCoefficientFlux
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω))
    (smoothFeedbackCellAffineResidual M m Q e ω) x).2

/-- The source directional Gram quadratic `e·Gamma_U e`, formed from the
actual affine-top minimizer defect and its reciprocal gradient. -/
noncomputable def smoothFeedbackCellDirectionalGamma (M : ABKModel 2)
    (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  vectorWeakHaarEnergy Q
      (smoothFeedbackCellAffineTopDefect M m Q e ω) +
    vectorWeakHaarEnergy Q
      (smoothFeedbackCellAffineReciprocalGradient M m Q e ω)

/-- The weak Haar energy only depends on the almost-everywhere class on the
open source cell. -/
theorem smooth_feedback_vector_weak_energy_congr_ae
    (Q : TriadicCube 2) {F G : Vec 2 → Vec 2}
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    vectorWeakHaarEnergy Q F = vectorWeakHaarEnergy Q G := by
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  have hfi : (fun x => F x i) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => G x i) := hFG.mono fun x hx => congrArg (fun v : Vec 2 => v i) hx
  have hproj (k : ℕ) : cubeProjection Q k (fun x => F x i) =
      cubeProjection Q k (fun x => G x i) :=
    Cold.square_scalar_projection_congr_ae Q k hfi
  have hinc (k : ℕ) :
      cubeIncrement Q k (fun x => F x i) = cubeIncrement Q k (fun x => G x i) := by
    cases k with
    | zero => simpa only [cubeIncrement_zero] using hproj 0
    | succ k => rw [cubeIncrement_succ, cubeIncrement_succ, hproj k, hproj (k + 1)]
  have henergy (k : ℕ) : energy Q (cubeIncrement Q k (fun x => F x i)) =
      energy Q (cubeIncrement Q k (fun x => G x i)) := congrArg (energy Q) (hinc k)
  change dualEnergy Q (Real.sqrt 3) (fun x => F x i) =
    dualEnergy Q (Real.sqrt 3) (fun x => G x i)
  unfold dualEnergy primalEnergy
  rw [henergy 0]
  congr 1
  apply tsum_congr
  intro k
  rw [henergy (k + 1)]

/-- A fixed Haar level of the vector energy is unchanged when the source fields
agree almost everywhere on the open source cell. -/
theorem smooth_feedback_vector_projected_energy_congr_ae
    (Q : TriadicCube 2) (depth : ℕ) {F G : Vec 2 → Vec 2}
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    (∑ i, energy Q (cubeProjection Q depth (fun x => F x i))) =
      ∑ i, energy Q (cubeProjection Q depth (fun x => G x i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  have hfi : (fun x => F x i) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => G x i) := hFG.mono fun x hx => congrArg (fun v : Vec 2 => v i) hx
  exact congrArg (energy Q) (Cold.square_scalar_projection_congr_ae Q depth hfi)

/-- The affine-top defect is homogeneous in its constant load, almost
everywhere on the source cell. -/
theorem smooth_feedback_affine_top_defect_smul_ae
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (c : ℝ) (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellAffineTopDefect M m Q (c • e) ω =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => c • smoothFeedbackCellAffineTopDefect M m Q e ω x) := by
  filter_upwards [smooth_feedback_affine_residual_smul_ae M m Q c e ω] with x hx
  have hfirst := congrArg Prod.fst hx
  funext i
  simp only [smoothFeedbackCellAffineTopDefect, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [hfirst]
  simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  ring

/-- The reciprocal-gradient field is homogeneous in its constant load,
almost everywhere on the source cell. -/
theorem smooth_feedback_affine_reciprocal_gradient_smul_ae
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (c : ℝ) (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellAffineReciprocalGradient M m Q (c • e) ω =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => c • smoothFeedbackCellAffineReciprocalGradient M m Q e ω x) := by
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
    (oldCutoffSkewCoefficient m Q ω)
  filter_upwards [smooth_feedback_affine_residual_smul_ae M m Q c e ω] with x hx
  change (blockMatVecMul (blockCoeffField a x)
      (smoothFeedbackCellAffineResidual M m Q (c • e) ω x)).2 =
    c • (blockMatVecMul (blockCoeffField a x)
      (smoothFeedbackCellAffineResidual M m Q e ω x)).2
  rw [hx, blockMatVecMul_smul]
  rfl

/-- The affine-top defect is additive in its deterministic load, almost
everywhere on the source cell. -/
theorem smooth_feedback_affine_top_defect_add_ae
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (e f : Vec 2) (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellAffineTopDefect M m Q (e + f) ω =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => smoothFeedbackCellAffineTopDefect M m Q e ω x +
        smoothFeedbackCellAffineTopDefect M m Q f ω x) := by
  filter_upwards [smooth_feedback_affine_residual_add_ae M m Q e f ω] with x hx
  have hfirst := congrArg Prod.fst hx
  have hfirst' : (smoothFeedbackCellAffineResidual M m Q (e + f) ω x).1 =
      (smoothFeedbackCellAffineResidual M m Q e ω x).1 +
        (smoothFeedbackCellAffineResidual M m Q f ω x).1 := by
    simpa using hfirst
  funext i
  have hfirsti :
      (smoothFeedbackCellAffineResidual M m Q (e + f) ω x).1 i =
        (smoothFeedbackCellAffineResidual M m Q e ω x).1 i +
          (smoothFeedbackCellAffineResidual M m Q f ω x).1 i := by
    simpa only [Pi.add_apply] using
      congrArg (fun v : Vec 2 => v i) hfirst'
  simp only [smoothFeedbackCellAffineTopDefect, Pi.sub_apply,
    Pi.add_apply]
  rw [hfirsti]
  ring

/-- The reciprocal-gradient field is additive in its deterministic load,
almost everywhere on the source cell. -/
theorem smooth_feedback_affine_reciprocal_gradient_add_ae
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (e f : Vec 2) (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellAffineReciprocalGradient M m Q (e + f) ω =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => smoothFeedbackCellAffineReciprocalGradient M m Q e ω x +
        smoothFeedbackCellAffineReciprocalGradient M m Q f ω x) := by
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
    (oldCutoffSkewCoefficient m Q ω)
  filter_upwards [smooth_feedback_affine_residual_add_ae M m Q e f ω] with x hx
  change (blockMatVecMul (blockCoeffField a x)
      (smoothFeedbackCellAffineResidual M m Q (e + f) ω x)).2 =
    (blockMatVecMul (blockCoeffField a x)
      (smoothFeedbackCellAffineResidual M m Q e ω x)).2 +
    (blockMatVecMul (blockCoeffField a x)
      (smoothFeedbackCellAffineResidual M m Q f ω x)).2
  rw [hx, blockMatVecMul_add]
  rfl

/-- The actual directional affine Gram is nonnegative on every OLD sample. -/
theorem smooth_feedback_cell_directional_gamma_nonneg
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ smoothFeedbackCellDirectionalGamma M m Q e ω := by
  unfold smoothFeedbackCellDirectionalGamma
  exact add_nonneg
    (vectorWeakHaarEnergy_nonneg Q _)
    (vectorWeakHaarEnergy_nonneg Q _)

/-- The local trace excess is exactly the full trace of the actual framed
coarse response minus four. -/
theorem smooth_feedback_cell_t_eq_full_trace (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellT M m Q ω =
      Matrix.trace (toFullBlockMat (smoothFeedbackCellA M m Q ω)) - 4 := by
  simpa [smoothFeedbackCellT, smoothFeedbackCellA,
    Cold.coldNativeResponse] using
    (Cold.coldNativeResponse_trace M m Q ω).symm

/-- The same trace excess is the sum of the actual affine-top and reciprocal
diagonal traces, minus four. -/
theorem smooth_feedback_cell_t_eq_block_traces (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellT M m Q ω =
      Matrix.trace (smoothFeedbackCellK M m Q ω) +
        Matrix.trace (smoothFeedbackCellD M m Q ω) - 4 := by
  rw [smooth_feedback_cell_t_eq_full_trace]
  simp [smoothFeedbackCellA, smoothFeedbackCellK,
    smoothFeedbackCellD, Matrix.trace, toFullBlockMat,
    Fintype.sum_sum_type]

/-- The source trace excess of an actual local response is nonnegative. -/
theorem smooth_feedback_cell_t_nonneg (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    0 ≤ smoothFeedbackCellT M m Q ω :=
  Cold.coldNativeCellTrace_nonneg M m Q ω

/-- The full symmetrized Gram defect of the actual framed cell response. -/
def smoothFeedbackCellGram (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) : FullBlockMat 2 :=
  (1 / 2 : ℝ) • (toFullBlockMat (smoothFeedbackCellA M m Q ω) +
    Cold.coarseGramSwap * toFullBlockMat (smoothFeedbackCellA M m Q ω) *
      Cold.coarseGramSwap) - 1

/-- The top-left block of the actual symmetrized Gram defect in the true
frame. Its trace is half the full response trace excess. -/
def smoothFeedbackCellGramTop (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) : Mat 2 :=
  (smoothFeedbackCellGram M m Q ω).submatrix Sum.inl Sum.inl

private theorem smooth_feedback_cell_symmetrized_gram_posSemidef
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    (smoothFeedbackCellGram M m Q ω).PosSemidef := by
  let A := toFullBlockMat (smoothFeedbackCellA M m Q ω)
  let R := Cold.coarseGramSwap
  let G := (1 / 2 : ℝ) • (A + R * A * R) - 1
  let T := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) A
  let S := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) R
  change G.PosSemidef
  obtain ⟨Λ, hEll⟩ := Cold.coldNativeCoefficient_elliptic M m Q ω
  have hEllOpen := hEll.mono (measurableSet_openCubeSet Q)
    (openCubeSet_subset_cubeSet Q)
  have hAeq : A = toFullBlockMat
      (coarseBlockMatrix (openCubeSet Q)
        (Cold.coldNativeCoefficient M m ω).toFun) := by
    change Cold.coldNativeResponse M m Q ω = _
    exact Cold.coldNativeResponse_eq_normalized M m Q ω
  have hAherm : A.IsHermitian := by
    rw [hAeq]
    exact Cold.coarse_square_full_isHermitian Q hEllOpen
  have hRherm : R.IsHermitian := Cold.coarseGramSwap_isHermitian
  have hRAR : (R * A * R).IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul R hAherm
    simpa only [hRherm.eq] using h
  have hGherm : G.IsHermitian := by
    dsimp [G]
    exact ((hAherm.add hRAR).smul
      (show IsSelfAdjoint (1 / 2 : ℝ) by simp)).sub Matrix.isHermitian_one
  have hSsym : S.toLinearMap.IsSymmetric := by
    change ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) R).toLinearMap.IsSymmetric
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hRherm
  have hSsq (x : EuclideanSpace ℝ (BlockCoord 2)) : S (S x) = x := by
    change R.toEuclideanLin (R.toEuclideanLin x) = x
    exact Cold.coarseGramSwap_involutive x
  have hplus : ∀ x : EuclideanSpace ℝ (BlockCoord 2),
      0 ≤ inner ℝ x (T x + S x) := by
    intro x
    have hs := Cold.coarse_square_gram_signs Q hEllOpen x
    change 0 ≤ inner ℝ x (
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2))
        (toFullBlockMat (coarseBlockMatrix (openCubeSet Q)
          (Cold.coldNativeCoefficient M m ω).toFun)) x +
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) R x) ∧ _ at hs
    rw [← hAeq] at hs
    exact hs.1
  have hminus : ∀ x : EuclideanSpace ℝ (BlockCoord 2),
      0 ≤ inner ℝ x (T x - S x) := by
    intro x
    have hs := Cold.coarse_square_gram_signs Q hEllOpen x
    change 0 ≤ inner ℝ x (
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2))
        (toFullBlockMat (coarseBlockMatrix (openCubeSet Q)
          (Cold.coldNativeCoefficient M m ω).toFun)) x +
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) R x) ∧
      0 ≤ inner ℝ x (
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2))
          (toFullBlockMat (coarseBlockMatrix (openCubeSet Q)
            (Cold.coldNativeCoefficient M m ω).toFun)) x -
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) R x) at hs
    rw [← hAeq] at hs
    exact hs.2
  have hGram : Cold.gramSymmetrizedDefect T S =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) G := by
    dsimp [Cold.gramSymmetrizedDefect, T, S, G, A, R]
    simp only [map_sub, map_smul, map_add, map_mul, map_one]
    rfl
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hGherm, ?_⟩
  intro v
  let x : EuclideanSpace ℝ (BlockCoord 2) := WithLp.toLp 2 v
  have hnonneg := Cold.gramSymmetrizedDefect_nonneg T S hSsym hSsq
    hplus hminus x
  rw [hGram] at hnonneg
  have hmatrix := Cold.matrix_euclidean_inner G x
  have hx : x.ofLp = v := rfl
  rw [hx] at hmatrix
  have hq : 0 ≤ v ⬝ᵥ G.mulVec v := by
    rw [← hmatrix]
    exact hnonneg
  simpa using hq

private theorem matrix_euclidean_inner' (B : Mat 2)
    (x : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)) B x) =
      x.ofLp ⬝ᵥ (B.mulVec x.ofLp) := by
  change inner ℝ x (B.toEuclideanLin x) = _
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, star_trivial, dotProduct_comm]

private theorem psd_planar_quadratic_le_trace (B : Mat 2)
    (hB : B.PosSemidef) (w : Vec 2) :
    vecDot w (matVecMul B w) ≤ Matrix.trace B * vecNormSq w := by
  let H := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)) B
  have hSym : H.toLinearMap.IsSymmetric := by
    change ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)) B).toLinearMap.IsSymmetric
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hB.isHermitian
  have hPos : ∀ x : EuclideanSpace ℝ (Fin 2),
      0 ≤ inner ℝ x (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)) B) x) := by
    intro x
    have h := hB.dotProduct_mulVec_nonneg x.ofLp
    have he := matrix_euclidean_inner' B x
    change 0 ≤ inner ℝ x ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)) B x)
    rw [he]
    simpa using h
  have hnorm := Cold.norm_le_trace_of_positive_operator H hSym hPos
  have htrace : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2)) H.toLinearMap =
      Matrix.trace B := by
    change LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2))
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) B).toLinearMap) = _
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      Cold.trace_toEuclideanLin]
  rw [htrace] at hnorm
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 w
  have hquad := Cold.inner_operator_le_norm_sq H x
  have he := matrix_euclidean_inner' B x
  have hx : x.ofLp = w := rfl
  rw [hx] at he
  change inner ℝ x ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)) B x) ≤ _ at hquad
  rw [he] at hquad
  have hxx : inner ℝ x x = vecNormSq w := by
    simp [x, vecNormSq, vecDot, Fin.sum_univ_two]
    ring
  rw [hxx] at hquad
  have hnormmul := mul_le_mul_of_nonneg_right hnorm (vecNormSq_nonneg w)
  have hresult := hquad.trans hnormmul
  simpa [x, H, vecDot, matVecMul, Matrix.mulVec_apply_eq_sum,
    Fin.sum_univ_two] using hresult

private theorem smooth_feedback_cell_gramTop_trace (M : ABKModel 2)
    (m : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    Matrix.trace (smoothFeedbackCellGramTop M m Q ω) =
      smoothFeedbackCellT M m Q ω / 2 := by
  rw [Matrix.trace_fin_two]
  have hentry (i : Fin 2) :
      smoothFeedbackCellGramTop M m Q ω i i =
        (1 / 2 : ℝ) *
          (smoothFeedbackCellK M m Q ω i i +
            smoothFeedbackCellD M m Q ω i i) - 1 := by
    simp [smoothFeedbackCellGramTop, Cold.coarseGramSwap,
      smoothFeedbackCellGram, smoothFeedbackCellK, smoothFeedbackCellD,
      toFullBlockMat, Book.Ch02.blockR, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply]
    ring
  rw [hentry 0, hentry 1, smooth_feedback_cell_t_eq_block_traces]
  simp [Matrix.trace_fin_two]
  ring

/-- Pathwise smooth-feedback pair charge is nonnegative and is bounded by
the actual trace excess of that cell. This uses the actual response duality
and the trace of its symmetrized Gram defect. -/
theorem smooth_feedback_cell_pair_charge_bounds (M : ABKModel 2)
    (m : ℤ) (Q : TriadicCube 2) (w : Vec 2)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ smoothFeedbackPairCharge M m Q w ω ∧
      smoothFeedbackPairCharge M m Q w ω ≤
        smoothFeedbackCellT M m Q ω * vecNormSq w := by
  let B := smoothFeedbackCellGramTop M m Q ω
  have hB := (smooth_feedback_cell_symmetrized_gram_posSemidef M m Q ω).submatrix Sum.inl
  have hq0 : 0 ≤ vecDot w (matVecMul B w) := by
    have h := hB.dotProduct_mulVec_nonneg w
    change 0 ≤ dotProduct w (B.mulVec w)
    simpa [dotProduct, B, smoothFeedbackCellGramTop] using h
  have hqle := psd_planar_quadratic_le_trace B hB w
  have hpair : smoothFeedbackPairCharge M m Q w ω =
      2 * vecDot w (matVecMul B w) := by
    simp [B, smoothFeedbackPairCharge, smoothFeedbackCellGramTop,
      smoothFeedbackCellK, smoothFeedbackCellD,
      smoothFeedbackCellGram, vecDot, matVecMul, vecNormSq,
      toFullBlockMat,
      Cold.coarseGramSwap, Book.Ch02.blockR, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two]
    ring_nf
  rw [hpair]
  have htrace := smooth_feedback_cell_gramTop_trace M m Q ω
  constructor
  · positivity
  · rw [htrace] at hqle
    nlinarith [hqle, vecNormSq_nonneg w]

/-- The actual OLD-frame response on a source cell has the true-frame
isotropic annealed block mean. -/
theorem smooth_feedback_cell_mean_blocks (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) :
    ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧
      Cold.matrixMean (Cutoff.cutoffSampleLaw M).toMeasure
        (fun ω => toFullBlockMat (smoothFeedbackCellA M m Q ω)) =
          1 + Cold.coldGraphBlockMean p q := by
  change ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧
    Cold.matrixMean (Cutoff.cutoffSampleLaw M).toMeasure
      (Cold.coldNativeResponse M m Q) = 1 + Cold.coldGraphBlockMean p q
  exact Cold.coldNativeResponse_mean_blocks M m Q

/-- The actual affine and reciprocal diagonal blocks inherit the scalar
true-frame means from the full response law. -/
theorem smooth_feedback_cell_mean_diagonal_blocks (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) :
    ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧
      Cold.matrixMean (Cutoff.cutoffSampleLaw M).toMeasure
        (fun ω => smoothFeedbackCellK M m Q ω) =
          (1 + p) • (1 : Mat 2) ∧
      Cold.matrixMean (Cutoff.cutoffSampleLaw M).toMeasure
        (fun ω => smoothFeedbackCellD M m Q ω) =
          (1 + q) • (1 : Mat 2) := by
  obtain ⟨p, q, hp, hq, hmean⟩ := smooth_feedback_cell_mean_blocks M m Q
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · ext i j
    have hentry := congrArg (fun A : FullBlockMat 2 => A (Sum.inl i) (Sum.inl j)) hmean
    calc
      _ = (if i = j then (1 : ℝ) else 0) + (if i = j then p else 0) := by
        simpa [Cold.matrixMean, smoothFeedbackCellK, smoothFeedbackCellA,
          Cold.coldGraphBlockMean, toFullBlockMat, Book.Ch02.blockDiag,
          Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] using hentry
      _ = _ := by
        simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
        split_ifs <;> ring
  · ext i j
    have hentry := congrArg (fun A : FullBlockMat 2 => A (Sum.inr i) (Sum.inr j)) hmean
    calc
      _ = (if i = j then (1 : ℝ) else 0) + (if i = j then q else 0) := by
        simpa [Cold.matrixMean, smoothFeedbackCellD, smoothFeedbackCellA,
          Cold.coldGraphBlockMean, toFullBlockMat, Book.Ch02.blockDiag,
          Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] using hentry
      _ = _ := by
        simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
        split_ifs <;> ring

/-- The annealed directional diagonal response excess equals one half the
annealed cell trace excess times the squared load. This is the actual-cell
`A_pair` identity, with the two diagonal blocks kept separate. -/
theorem smooth_feedback_cell_mean_pair_quadratic (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (w : Vec 2) :
    (∫ ω, smoothFeedbackPairCharge M m Q w ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      (1 / 2 : ℝ) *
        (∫ ω, smoothFeedbackCellT M m Q ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) * vecNormSq w := by
  change (∫ ω, vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w) +
      vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w) -
      2 * vecNormSq w ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  obtain ⟨p, q, hp, hq, hKmean, hDmean⟩ :=
    smooth_feedback_cell_mean_diagonal_blocks M m Q
  have hKentry : ∀ i j : Fin 2,
      Integrable (fun ω => smoothFeedbackCellK M m Q ω i j) μ := by
    intro i j
    change Integrable
      (fun ω => Cold.coldNativeResponse M m Q ω (Sum.inl i) (Sum.inl j)) μ
    exact smooth_feedback_response_entry_integrable M m Q (Sum.inl i) (Sum.inl j)
  have hDentry : ∀ i j : Fin 2,
      Integrable (fun ω => smoothFeedbackCellD M m Q ω i j) μ := by
    intro i j
    change Integrable
      (fun ω => Cold.coldNativeResponse M m Q ω (Sum.inr i) (Sum.inr j)) μ
    exact smooth_feedback_response_entry_integrable M m Q (Sum.inr i) (Sum.inr j)
  let P : Mat 2 := fun i j => w i * w j
  have hrepr (A : Mat 2) :
      vecDot w (matVecMul A w) = Cold.matrixFrobeniusInner P A := by
    simp only [vecDot, matVecMul, Cold.matrixFrobeniusInner, P, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hscalar (c : ℝ) :
      Cold.matrixFrobeniusInner P (c • (1 : Mat 2)) = c * vecNormSq w := by
    simp [Cold.matrixFrobeniusInner, P, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, vecNormSq, vecDot, Fin.sum_univ_two]
    ring
  have hKinnerInt : Integrable
      (fun ω => Cold.matrixFrobeniusInner P (smoothFeedbackCellK M m Q ω)) μ := by
    unfold Cold.matrixFrobeniusInner
    exact integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hKentry i j).const_mul (P i j)))
  have hDInnerInt : Integrable
      (fun ω => Cold.matrixFrobeniusInner P (smoothFeedbackCellD M m Q ω)) μ := by
    unfold Cold.matrixFrobeniusInner
    exact integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hDentry i j).const_mul (P i j)))
  have hKquadInt : Integrable
      (fun ω => vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w)) μ :=
    hKinnerInt.congr (Filter.Eventually.of_forall fun ω => (hrepr _).symm)
  have hDquadInt : Integrable
      (fun ω => vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w)) μ :=
    hDInnerInt.congr (Filter.Eventually.of_forall fun ω => (hrepr _).symm)
  have hKquad :
      (∫ ω, vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w) ∂μ) =
        (1 + p) * vecNormSq w := by
    calc
      _ = ∫ ω, Cold.matrixFrobeniusInner P
          (smoothFeedbackCellK M m Q ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        exact hrepr _
      _ = Cold.matrixFrobeniusInner P
          (Cold.matrixMean μ (fun ω => smoothFeedbackCellK M m Q ω)) :=
        Cold.integral_matrixFrobeniusInner_const P
          (fun ω => smoothFeedbackCellK M m Q ω) hKentry
      _ = (1 + p) * vecNormSq w := by rw [hKmean, hscalar]
  have hDquad :
      (∫ ω, vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w) ∂μ) =
        (1 + q) * vecNormSq w := by
    calc
      _ = ∫ ω, Cold.matrixFrobeniusInner P
          (smoothFeedbackCellD M m Q ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        exact hrepr _
      _ = Cold.matrixFrobeniusInner P
          (Cold.matrixMean μ (fun ω => smoothFeedbackCellD M m Q ω)) :=
        Cold.integral_matrixFrobeniusInner_const P
          (fun ω => smoothFeedbackCellD M m Q ω) hDentry
      _ = (1 + q) * vecNormSq w := by rw [hDmean, hscalar]
  have hKtraceInt : Integrable
      (fun ω => Matrix.trace (smoothFeedbackCellK M m Q ω)) μ := by
    unfold Matrix.trace
    exact integrable_finsetSum Finset.univ (fun i _ => hKentry i i)
  have hDtraceInt : Integrable
      (fun ω => Matrix.trace (smoothFeedbackCellD M m Q ω)) μ := by
    unfold Matrix.trace
    exact integrable_finsetSum Finset.univ (fun i _ => hDentry i i)
  have hTmean :
      (∫ ω, smoothFeedbackCellT M m Q ω ∂μ) = 2 * (p + q) := by
    calc
      _ = ∫ ω, Matrix.trace (smoothFeedbackCellK M m Q ω) +
          Matrix.trace (smoothFeedbackCellD M m Q ω) - 4 ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        exact smooth_feedback_cell_t_eq_block_traces M m Q ω
      _ = 2 * (p + q) := by
        rw [integral_sub (f := fun ω =>
            Matrix.trace (smoothFeedbackCellK M m Q ω) +
              Matrix.trace (smoothFeedbackCellD M m Q ω))
            (g := fun _ => (4 : ℝ)) (hKtraceInt.add hDtraceInt)
            (integrable_const 4),
          integral_add (f := fun ω => Matrix.trace (smoothFeedbackCellK M m Q ω))
            (g := fun ω => Matrix.trace (smoothFeedbackCellD M m Q ω))
            hKtraceInt hDtraceInt]
        rw [Cold.integral_matrix_trace _ (fun i => hKentry i i),
          Cold.integral_matrix_trace _ (fun i => hDentry i i), hKmean, hDmean]
        simp [Matrix.trace, Matrix.smul_apply, smul_eq_mul, probReal_univ]
        ring
  calc
    _ = (∫ ω, vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w) ∂μ) +
          (∫ ω, vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w) ∂μ) -
          2 * vecNormSq w := by
        rw [integral_sub (f := fun ω =>
            vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w) +
              vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w))
            (g := fun _ => 2 * vecNormSq w) (hKquadInt.add hDquadInt)
            (integrable_const (2 * vecNormSq w)),
          integral_add (f := fun ω =>
            vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w))
            (g := fun ω =>
              vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w))
            hKquadInt hDquadInt]
        simp [probReal_univ]
    _ = (1 / 2 : ℝ) * (∫ ω, smoothFeedbackCellT M m Q ω ∂μ) * vecNormSq w := by
        rw [hKquad, hDquad, hTmean]
        ring

/-- The actual-cell directional diagonal response charge is integrable on the
cutoff law, with integrability derived from the cell trace. -/
theorem smooth_feedback_cell_pair_charge_integrable (M : ABKModel 2)
    (m : ℤ) (Q : TriadicCube 2) (w : Vec 2) :
    Integrable (fun ω => smoothFeedbackPairCharge M m Q w ω)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hKentry : ∀ i j : Fin 2,
      Integrable (fun ω => smoothFeedbackCellK M m Q ω i j) μ := by
    intro i j
    change Integrable
      (fun ω => Cold.coldNativeResponse M m Q ω (Sum.inl i) (Sum.inl j)) μ
    exact smooth_feedback_response_entry_integrable M m Q (Sum.inl i) (Sum.inl j)
  have hDentry : ∀ i j : Fin 2,
      Integrable (fun ω => smoothFeedbackCellD M m Q ω i j) μ := by
    intro i j
    change Integrable
      (fun ω => Cold.coldNativeResponse M m Q ω (Sum.inr i) (Sum.inr j)) μ
    exact smooth_feedback_response_entry_integrable M m Q (Sum.inr i) (Sum.inr j)
  let P : Mat 2 := fun i j => w i * w j
  have hrepr (A : Mat 2) :
      vecDot w (matVecMul A w) = Cold.matrixFrobeniusInner P A := by
    simp only [vecDot, matVecMul, Cold.matrixFrobeniusInner, P, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hKinnerInt : Integrable
      (fun ω => Cold.matrixFrobeniusInner P (smoothFeedbackCellK M m Q ω)) μ := by
    unfold Cold.matrixFrobeniusInner
    exact integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hKentry i j).const_mul (P i j)))
  have hDInnerInt : Integrable
      (fun ω => Cold.matrixFrobeniusInner P (smoothFeedbackCellD M m Q ω)) μ := by
    unfold Cold.matrixFrobeniusInner
    exact integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hDentry i j).const_mul (P i j)))
  have hKquadInt : Integrable
      (fun ω => vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w)) μ :=
    hKinnerInt.congr (Filter.Eventually.of_forall fun ω => (hrepr _).symm)
  have hDquadInt : Integrable
      (fun ω => vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w)) μ :=
    hDInnerInt.congr (Filter.Eventually.of_forall fun ω => (hrepr _).symm)
  change Integrable (fun ω =>
    vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w) +
      vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w) -
      2 * vecNormSq w) μ
  exact (hKquadInt.add hDquadInt).sub (integrable_const _)

/-- The two annealed diagonal block quadratics are separately controlled by
the actual OLD trace cap.  This is the `P_K` and `P_D` input in Λ8. -/
theorem smooth_feedback_cell_mean_diagonal_quadratic_le
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (w : Vec 2)
    {a5 : ℝ}
    (hTcap : (∫ ω, smoothFeedbackCellT M m Q ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ a5) :
    (∫ ω, vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (1 + a5 / 2) * vecNormSq w ∧
    (∫ ω, vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (1 + a5 / 2) * vecNormSq w := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  obtain ⟨p, q, hp, hq, hKmean, hDmean⟩ :=
    smooth_feedback_cell_mean_diagonal_blocks M m Q
  have hKentry : ∀ i j : Fin 2,
      Integrable (fun ω => smoothFeedbackCellK M m Q ω i j) μ := by
    intro i j
    change Integrable
      (fun ω => Cold.coldNativeResponse M m Q ω (Sum.inl i) (Sum.inl j)) μ
    exact smooth_feedback_response_entry_integrable M m Q
      (Sum.inl i) (Sum.inl j)
  have hDentry : ∀ i j : Fin 2,
      Integrable (fun ω => smoothFeedbackCellD M m Q ω i j) μ := by
    intro i j
    change Integrable
      (fun ω => Cold.coldNativeResponse M m Q ω (Sum.inr i) (Sum.inr j)) μ
    exact smooth_feedback_response_entry_integrable M m Q
      (Sum.inr i) (Sum.inr j)
  let P : Mat 2 := fun i j => w i * w j
  have hrepr (A : Mat 2) :
      vecDot w (matVecMul A w) = Cold.matrixFrobeniusInner P A := by
    simp only [vecDot, matVecMul, Cold.matrixFrobeniusInner, P, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hscalar (c : ℝ) :
      Cold.matrixFrobeniusInner P (c • (1 : Mat 2)) = c * vecNormSq w := by
    simp [Cold.matrixFrobeniusInner, P, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, vecNormSq, vecDot, Fin.sum_univ_two]
    ring
  have hKinnerInt : Integrable
      (fun ω => Cold.matrixFrobeniusInner P
        (smoothFeedbackCellK M m Q ω)) μ := by
    unfold Cold.matrixFrobeniusInner
    exact integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        (hKentry i j).const_mul (P i j)))
  have hDinnerInt : Integrable
      (fun ω => Cold.matrixFrobeniusInner P
        (smoothFeedbackCellD M m Q ω)) μ := by
    unfold Cold.matrixFrobeniusInner
    exact integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        (hDentry i j).const_mul (P i j)))
  have hKquadInt : Integrable
      (fun ω => vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w)) μ :=
    hKinnerInt.congr (Filter.Eventually.of_forall fun ω => (hrepr _).symm)
  have hDquadInt : Integrable
      (fun ω => vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w)) μ :=
    hDinnerInt.congr (Filter.Eventually.of_forall fun ω => (hrepr _).symm)
  have hKquad :
      (∫ ω, vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w) ∂μ) =
        (1 + p) * vecNormSq w := by
    calc
      _ = ∫ ω, Cold.matrixFrobeniusInner P
          (smoothFeedbackCellK M m Q ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        exact hrepr _
      _ = Cold.matrixFrobeniusInner P
          (Cold.matrixMean μ (fun ω => smoothFeedbackCellK M m Q ω)) :=
        Cold.integral_matrixFrobeniusInner_const P
          (fun ω => smoothFeedbackCellK M m Q ω) hKentry
      _ = (1 + p) * vecNormSq w := by rw [hKmean, hscalar]
  have hDquad :
      (∫ ω, vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w) ∂μ) =
        (1 + q) * vecNormSq w := by
    calc
      _ = ∫ ω, Cold.matrixFrobeniusInner P
          (smoothFeedbackCellD M m Q ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        exact hrepr _
      _ = Cold.matrixFrobeniusInner P
          (Cold.matrixMean μ (fun ω => smoothFeedbackCellD M m Q ω)) :=
        Cold.integral_matrixFrobeniusInner_const P
          (fun ω => smoothFeedbackCellD M m Q ω) hDentry
      _ = (1 + q) * vecNormSq w := by rw [hDmean, hscalar]
  have hKtraceInt : Integrable
      (fun ω => Matrix.trace (smoothFeedbackCellK M m Q ω)) μ := by
    unfold Matrix.trace
    exact integrable_finsetSum Finset.univ (fun i _ => hKentry i i)
  have hDtraceInt : Integrable
      (fun ω => Matrix.trace (smoothFeedbackCellD M m Q ω)) μ := by
    unfold Matrix.trace
    exact integrable_finsetSum Finset.univ (fun i _ => hDentry i i)
  have hTmean :
      (∫ ω, smoothFeedbackCellT M m Q ω ∂μ) = 2 * (p + q) := by
    calc
      _ = ∫ ω, Matrix.trace (smoothFeedbackCellK M m Q ω) +
          Matrix.trace (smoothFeedbackCellD M m Q ω) - 4 ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        exact smooth_feedback_cell_t_eq_block_traces M m Q ω
      _ = 2 * (p + q) := by
        rw [integral_sub (f := fun ω =>
            Matrix.trace (smoothFeedbackCellK M m Q ω) +
              Matrix.trace (smoothFeedbackCellD M m Q ω))
            (g := fun _ => (4 : ℝ)) (hKtraceInt.add hDtraceInt)
            (integrable_const 4),
          integral_add (f := fun ω => Matrix.trace (smoothFeedbackCellK M m Q ω))
            (g := fun ω => Matrix.trace (smoothFeedbackCellD M m Q ω))
            hKtraceInt hDtraceInt]
        rw [Cold.integral_matrix_trace _ (fun i => hKentry i i),
          Cold.integral_matrix_trace _ (fun i => hDentry i i), hKmean, hDmean]
        simp [Matrix.trace, Matrix.smul_apply, smul_eq_mul, probReal_univ]
        ring
  have hpq : p + q ≤ a5 / 2 := by linarith [hTcap, hTmean]
  have hpbound : p ≤ a5 / 2 := by linarith [hq, hpq]
  have hqbound : q ≤ a5 / 2 := by linarith [hp, hpq]
  constructor
  · rw [hKquad]
    exact mul_le_mul_of_nonneg_right (by linarith) (vecNormSq_nonneg w)
  · rw [hDquad]
    exact mul_le_mul_of_nonneg_right (by linarith) (vecNormSq_nonneg w)

end
end ASDExplicitGamma.Scalar
