module

public import ASDExplicitGamma.Main.EnvelopeASlope
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocal
public import ASDExplicitGamma.Scalar.OldHessianTrialPatchDrop
public import ASDExplicitGamma.Native.OldSignedPartialFrameHistory
public import ASDExplicitGamma.Main.EnvelopeHMaxHistory
public import ASDExplicitGamma.Inverse.ParentGapCenteredDepth

/-! Package D, part one: the actual-law energy drop of the hot trial.  The
parent is the root cube `originCube 2 m`, the source tiling is its depth-five
descendants, and the frame is the OLD frame `sigmaBar M m`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- The hot-trial energy drop `Delta = sum_U weight_U tr A_U - tr A_Q` in
trace-defect form (the constants `-4` cancel): the depth-five average of the
actual four-load traces minus the actual root trace, in the OLD frame. -/
def mainHotDrop (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  descendantsAverage (originCube 2 m) 5
      (fun U => rawCubeFourLoadTrace M m U t ω) -
    rawCubeFourLoadTrace M m (originCube 2 m) t ω

theorem main_hot_descendants_average_congr (Q : TriadicCube 2)
    (depth : ℕ) (f g : TriadicCube 2 → ℝ)
    (hfg : ∀ R ∈ descendantsAtDepth Q depth, f R = g R) :
    descendantsAverage Q depth f = descendantsAverage Q depth g := by
  classical
  unfold descendantsAverage
  apply congrArg (fun t => ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * t)
  refine Finset.sum_congr rfl ?_
  intro R hR
  exact hfg R hR

/-- On every descendant cell the raw four-load trace is the framed trace of
the actual response coefficient. -/
theorem main_hot_trace_eq_frame_trace
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (j : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 m) j) :
    rawCubeFourLoadTrace M m U t ω =
      traceDefect (openCubeSet U)
        (oldSignedPartialFrameFieldAt M (originCube 2 m) m t ω) 1 := by
  unfold rawCubeFourLoadTrace traceDefect
  rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,
    old_signed_partial_cell_frame_at M (originCube 2 m) m t ω U j hU]
  simp only [Variational.frameMatrix, inv_one, one_mul, Matrix.trace_smul,
    smul_eq_mul]

/-- Pathwise energy-drop identity: `Delta` is the sum, over the four canonical
affine loads, of the actual energy of `S - L` (parent minimizer minus the
patch of local minimizers). -/
theorem main_hot_drop_pathwise_energy
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    mainHotDrop M m t ω =
      ∑ c : BlockCoord 2, oldHessianPatchDrop (originCube 2 m) 5 M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mainAffineOpenResponseRestriction (originCube 2 m)
          (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 m)))
            m t ω))
        (blockBasis c) ∧
    0 ≤ mainHotDrop M m t ω := by
  classical
  have hid := old_hessian_full_patch_trace_identity (originCube 2 m) 5 M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (mainAffineOpenResponseRestriction (originCube 2 m)
      (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 m)))
        m t ω))
  have heq : mainHotDrop M m t ω =
      ∑ c : BlockCoord 2, oldHessianPatchDrop (originCube 2 m) 5 M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mainAffineOpenResponseRestriction (originCube 2 m)
          (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 m)))
            m t ω))
        (blockBasis c) := by
    rw [hid]
    unfold mainHotDrop
    have hroot : originCube 2 m ∈ descendantsAtDepth (originCube 2 m) 0 := by
      simp only [descendantsAtDepth_zero, Finset.mem_singleton]
    have hcells :
        descendantsAverage (originCube 2 m) 5
          (fun U => rawCubeFourLoadTrace M m U t ω) =
        descendantsAverage (originCube 2 m) 5 (fun U =>
          traceDefect (openCubeSet U)
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainAffineOpenResponseRestriction (originCube 2 m)
                (Gaussian.modelInsertedScalar
                  (closure (cubeSet (originCube 2 m))) m t ω))) 1) := by
      refine main_hot_descendants_average_congr _ _ _ _ ?_
      intro U hU
      exact main_hot_trace_eq_frame_trace M m t ω 5 U hU
    rw [hcells, main_hot_trace_eq_frame_trace M m t ω 0 _ hroot]
    rfl
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Finset.sum_nonneg fun c _ =>
    old_hessian_patch_drop_nonneg _ _ _ _ _ _ _ _

private theorem main_hot_raw_depth_measurable
    (M : ABKModel 2) (m q : ℤ) (t : ℝ) :
    Measurable (rawDepthFourLoadTrace M m q t) := by
  let K := closure (cubeSet (originCube 2 q))
  have : CompactSpace K := modelHeatCubeClosureCompact q
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have hscalar : Measurable (modelInsertedScalar K m t) := by
    change Measurable (fun ω => olderField K m ω +
      Real.sqrt t • shellFieldScalarRestriction K (ω.1 (m + 1)))
    exact (measurable_olderField K ell m hK).add
      (((measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)).const_smul
          (Real.sqrt t))
  have hobs := (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1).1.continuous.measurable.comp hscalar
  have heq : rawDepthFourLoadTrace M m q t =
      fun ω => modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)
        (modelInsertedScalar K m t ω) := by
    funext ω
    exact raw_depth_four_load_trace_eq_model_observable M m q t ω
  rw [heq]
  exact hobs

/-- Every actual cell trace is measurable on the cutoff sample space. -/
theorem main_hot_raw_cube_measurable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ) :
    Measurable (rawCubeFourLoadTrace M m Q t) := by
  have heq : rawCubeFourLoadTrace M m Q t =
      fun ω => rawDepthFourLoadTrace M m Q.scale t
        (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
    funext ω
    exact main_rawCubeFourLoadTrace_translate_to_origin M m Q t ω
  rw [heq]
  exact (main_hot_raw_depth_measurable M m Q.scale t).comp
    (Cutoff.measurable_translateCutoffSample (triadicCubeShift Q))

/-- Actual-law energy-drop identity `E Delta = a - f`, with `a` the depth-five
mean and `f` the root mean, both in the OLD frame; `0 <= f <= a`, and
`E Delta <= mainEnvelopeA - f`. -/
theorem main_hot_energy_drop_identity
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable (mainHotDrop M m t) μ ∧
    (∫ ω, mainHotDrop M m t ω ∂μ) =
      inSourceMeanActual M m 5 t - inSourceMeanActual M m 0 t ∧
    0 ≤ inSourceMeanActual M m 0 t ∧
    inSourceMeanActual M m 0 t ≤ inSourceMeanActual M m 5 t ∧
    (∫ ω, mainHotDrop M m t ω ∂μ) ≤
      mainEnvelopeA
        ((q3ModelAmplitude M h (m + 1)) ^ 2 /
          (Annealed.sigmaBar M m : ℝ) ^ 2)
        M.gamma mainSourceMeanPrefix t -
      inSourceMeanActual M m 0 t := by
  classical
  intro μ
  let Q := originCube 2 m
  let T : TriadicCube 2 → Cutoff.CutoffSample 2 → ℝ :=
    fun U ω => rawCubeFourLoadTrace M m U t ω
  let a := inSourceMeanActual M m 5 t
  have hcell (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q 5) :
      Integrable (T U) μ ∧ (∫ ω, T U ω ∂μ) = a :=
    mixed_bridge_source_cell_raw_trace_mean M h hM hγ N hpast m hm t ht U hU
  have hcard : ((descendantsAtDepth Q 5).card : ℝ) ≠ 0 := by
    have hne : (descendantsAtDepth Q 5).Nonempty :=
      ⟨_, originCube_mem_descendantsAtDepth' 2 m 5⟩
    exact_mod_cast hne.card_pos.ne'
  have havgFun : (fun ω => descendantsAverage Q 5 (fun U => T U ω)) =
      fun ω => ((descendantsAtDepth Q 5).card : ℝ)⁻¹ *
        ∑ U ∈ descendantsAtDepth Q 5, T U ω := rfl
  have havgInt : Integrable (fun ω => descendantsAverage Q 5 (fun U => T U ω)) μ := by
    rw [havgFun]
    exact (integrable_finsetSum _ fun U hU => (hcell U hU).1).const_mul _
  have havgInteg : (∫ ω, descendantsAverage Q 5 (fun U => T U ω) ∂μ) = a := by
    rw [havgFun, integral_const_mul,
      integral_finsetSum _ fun U hU => (hcell U hU).1,
      Finset.sum_congr rfl fun U hU => (hcell U hU).2]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hΔnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ mainHotDrop M m t ω :=
    (main_hot_drop_pathwise_energy M m t ω).2
  have hrootNonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ T Q ω :=
    raw_cube_four_load_trace_nonneg M m Q t ⟨ht.1, ht.2⟩ ω
  have hrootLe (ω : Cutoff.CutoffSample 2) :
      T Q ω ≤ descendantsAverage Q 5 (fun U => T U ω) := by
    have := hΔnonneg ω
    unfold mainHotDrop at this
    exact sub_nonneg.mp this
  have hrootInt : Integrable (T Q) μ := by
    refine havgInt.mono' (main_hot_raw_cube_measurable M m Q t).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (hrootNonneg ω)]
    exact hrootLe ω
  have hfEq : (∫ ω, T Q ω ∂μ) = inSourceMeanActual M m 0 t := by
    simp [T, Q, inSourceMeanActual, modelTraceHeatAverage, rawCubeFourLoadTrace, μ]
  have hΔint : Integrable (mainHotDrop M m t) μ := havgInt.sub hrootInt
  have hΔeq : (∫ ω, mainHotDrop M m t ω ∂μ) =
      a - inSourceMeanActual M m 0 t := by
    unfold mainHotDrop
    rw [integral_sub havgInt hrootInt, havgInteg, hfEq]
  have hf0 : 0 ≤ inSourceMeanActual M m 0 t := by
    rw [← hfEq]
    exact integral_nonneg hrootNonneg
  have hΔge : 0 ≤ ∫ ω, mainHotDrop M m t ω ∂μ := integral_nonneg hΔnonneg
  have hA := main_envelope_a_actual_law M h hM hγ N hpast m hm ht
  refine ⟨hΔint, hΔeq, hf0, by linarith [hΔeq, hΔge], ?_⟩
  rw [hΔeq]
  have : a ≤ mainEnvelopeA
        ((q3ModelAmplitude M h (m + 1)) ^ 2 /
          (Annealed.sigmaBar M m : ℝ) ^ 2)
        M.gamma mainSourceMeanPrefix t := hA
  linarith

end

end ASDExplicitGamma.Main
