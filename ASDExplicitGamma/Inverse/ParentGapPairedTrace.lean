module

public import ASDExplicitGamma.Inverse.BridgeObservables
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Cold.NativeFrameTrace

/-! Parent-level paired weak-trace estimates in the actual OLD frame. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Response
  ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic

noncomputable section

private theorem symmPart_partialInserted (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    symmPart (Model.partialInsertedCoefficient M m t ω x) = M.nu • (1 : Mat 2) := by
  have ha := Cutoff.symmPart_coefficientCutoff M.nu m ω x
  ext i j
  have hb := congrFun (congrFun ha i) j
  have hj := (ω.1 (m + 1)).skew_entry x i j
  change (Cutoff.coefficientCutoff M.nu m ω x i j +
    Cutoff.coefficientCutoff M.nu m ω x j i) / 2 = (M.nu • (1 : Mat 2)) i j at hb
  change ((Cutoff.coefficientCutoff M.nu m ω x i j + Real.sqrt t * ω.1 (m + 1) x i j) +
    (Cutoff.coefficientCutoff M.nu m ω x j i + Real.sqrt t * ω.1 (m + 1) x j i)) / 2 = _
  rw [hj]
  linarith

/-- The parent response restriction is pointwise the normalized actual
partially inserted coefficient in the fixed OLD frame. -/
theorem mixed_bridge_frame_field_eq_inserted
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    {x : Vec 2} (hx : x ∈ openCubeSet (originCube 2 m)) :
    responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mixedBridgeResponseCoefficient m t ω) x =
      ((Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x) := by
  let Q := originCube 2 m
  let K := closure (cubeSet Q)
  let σ : ℝ := Annealed.sigmaBar M m
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure
  letI : CompactSpace (closure (openCubeSet Q)) :=
    isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure
  obtain ⟨ell, hKell⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet Q).isCompact_closure
  let xK : K := ⟨x, subset_closure (openCubeSet_subset_cubeSet Q hx)⟩
  have hscalar : responseCoefficientExtension (mixedBridgeResponseCoefficient m t ω) x =
      (Model.partialInsertedCoefficient M m t ω).toFun x 1 0 := by
    rw [responseCoefficientExtension_eq _ hx]
    change modelInsertedScalar K m t ω xK = _
    simpa [xK] using modelInsertedScalar_apply K M ell m hKell t ω xK
  have hentry : responseCoefficientExtension (mixedBridgeResponseCoefficient m t ω) x / σ =
      (σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun x) 1 0 := by
    rw [hscalar]
    simp [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hsymm := symmPart_partialInserted M m t ω x
  have hscaled : symmPart
      (σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun x) =
        (M.nu / σ) • (1 : Mat 2) := by
    rw [symmPart_smul, hsymm]
    simp [σ, div_eq_mul_inv, smul_smul, mul_comm]
  rw [responseFramePlanarCoefficientField_apply, hentry]
  exact planar_coefficient_eq_of_symmPart (M.nu / σ) _ hscaled

/-- The normalized OLD-frame inverse maximum at weak depth `j` is exactly
`σ̄_m` times the same depth maximum for the actual partial-insertion field.
This is the coefficient-frame identity needed to match the paired projection
proxy with the source inverse-history bank. -/
theorem mixed_bridge_frame_inverse_depth_eq_sigma_actual
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    lemmaVInverseDepthMax (originCube 2 m)
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mixedBridgeResponseCoefficient m t ω)) j =
      (Annealed.sigmaBar M m : ℝ) *
        lemmaVInverseDepthMax (originCube 2 m)
          (Model.partialInsertedCoefficient M m t ω).toFun j := by
  let Q := originCube 2 m
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mixedBridgeResponseCoefficient m t ω
  let a := (Model.partialInsertedCoefficient M m t ω).toFun
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hframeEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ k
  obtain ⟨ell, hKell⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet Q)) (isBounded_cubeSet Q).isCompact_closure
  have hInvAt (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j) :
      sigmaStarInvCoarse (openCubeSet R)
          (responseFramePlanarCoefficientField M.nu σ k) =
        σ • sigmaStarInvCoarse (openCubeSet R) a := by
    have hRsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR := Model.partialInsertedCoefficient_isEllipticFieldOn
      M ell m ω ⟨ht.1, ht.2⟩ (measurableSet_cubeSet R) (by
        intro x hx
        exact hKell (subset_closure (hRsub hx)))
    have hEllRopen :=
      hEllR.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
    have hframeR := hframeEll.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    have hfield : (fun x => responseFramePlanarCoefficientField M.nu σ k x) =ᵐ[
        volume.restrict (openCubeSet R)] (σ⁻¹ • a) := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      exact mixed_bridge_frame_field_eq_inserted M m t ω
        (openCubeSet_subset_of_mem_descendantsAtDepth hR hx)
    have hcoarse : coarseBlockMatrix (cubeSet R)
        (responseFramePlanarCoefficientField M.nu σ k) =
      coarseBlockMatrix (cubeSet R) (σ⁻¹ • a) := by
      rw [Cold.cold_coarse_cube_open R
          (responseFramePlanarCoefficientField M.nu σ k),
        Cold.cold_coarse_cube_open R (σ⁻¹ • a)]
      exact coarseBlockMatrix_congr_of_ae_eq hfield
    have hframeCoarse : coarseBlockMatrix (cubeSet R)
        (responseFramePlanarCoefficientField M.nu σ k) =
      frameMatrix σ (coarseBlockMatrix (cubeSet R) a) :=
      hcoarse.trans (Cold.cold_coarse_frame M.nu_pos hEllR hσ)
    calc
      _ = (coarseBlockMatrix (cubeSet R)
            (responseFramePlanarCoefficientField M.nu σ k)).lowerRight :=
        Scalar.inverse_history_lowerRight R
          (responseFramePlanarCoefficientField M.nu σ k) hframeR
      _ = (frameMatrix σ (coarseBlockMatrix (cubeSet R) a)).lowerRight :=
        congrArg BlockMat.lowerRight hframeCoarse
      _ = σ • sigmaStarInvCoarse (openCubeSet R) a := by
        simp only [Variational.frameMatrix]
        rw [← Scalar.inverse_history_lowerRight R a hEllRopen]
  unfold lemmaVInverseDepthMax
  rw [← Scalar.inverse_history_finset_max_mul
    (descendantsAtDepth Q j) (descendantsAtDepth_nonempty Q j)
    (fun R => Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) a))
    σ hσ]
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  rw [hInvAt R hR, Scalar.inverse_history_matrixNorm_smul
    (sigmaStarInvCoarse (openCubeSet R) a) σ hσ.le]

/-- Each actual partial-insertion trace on a child cube agrees with the
restriction of the exported response coefficient in the OLD frame. -/
theorem mixed_bridge_raw_cube_trace_eq_frame
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (j : ℕ)
    {U : TriadicCube 2} (hU : U ∈ descendantsAtDepth (originCube 2 m) j) :
    rawCubeFourLoadTrace M m U t ω =
      traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mixedBridgeResponseCoefficient m t ω)) 1 := by
  let Q := originCube 2 m
  let σ : ℝ := Annealed.sigmaBar M m
  obtain ⟨ell, hKell⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet Q)) (isBounded_cubeSet Q).isCompact_closure
  have hUcube : cubeSet U ⊆ openCubeSet (originCube 2 ell) := by
    intro x hx
    exact hKell (subset_closure
      ((cubeSet_subset_of_mem_descendantsAtDepth hU) hx))
  have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω
    ⟨ht.1, ht.2⟩ (measurableSet_cubeSet U) hUcube
  have hfield : ∀ x ∈ openCubeSet U,
      responseFramePlanarCoefficientField M.nu σ
        (mixedBridgeResponseCoefficient m t ω) x =
      (σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun) x := by
    intro x hx
    exact mixed_bridge_frame_field_eq_inserted M m t ω
      (openCubeSet_subset_of_mem_descendantsAtDepth hU hx)
  have hae := (ae_restrict_mem (μ := volume) (measurableSet_openCubeSet U)).mono hfield
  have htrace : traceDefect (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu σ
        (mixedBridgeResponseCoefficient m t ω)) 1 =
      traceDefect (openCubeSet U)
        (σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun) 1 := by
    unfold traceDefect
    rw [coarseBlockMatrix_congr_of_ae_eq hae]
  have hframe := Cold.cold_trace_frame M.nu_pos hEll
    (Annealed.sigmaBar_characterization M m).1
  change traceDefect (cubeSet U)
      (Model.partialInsertedCoefficient M m t ω).toFun σ = _
  exact hframe.symm.trans htrace.symm

/-- The projection-side child trace average in the response-frame
coefficient used by the actual parent minimizers. -/
noncomputable def mixedBridgeFrameTbar (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  let Q := originCube 2 m
  let k := mixedBridgeResponseCoefficient m t ω
  let σ : ℝ := Annealed.sigmaBar M m
  descendantsAverage Q j (fun U =>
    traceDefect (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu σ k) 1)

/-- The projection-side parent trace in the same OLD frame. -/
noncomputable def mixedBridgeFrameAnchorTrace (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 m
  let k := mixedBridgeResponseCoefficient m t ω
  let σ : ℝ := Annealed.sigmaBar M m
  traceDefect (openCubeSet Q)
    (responseFramePlanarCoefficientField M.nu σ k) 1

/-- The exported raw source trace average is exactly the descendant
average of unit-frame child traces. -/
theorem mixed_bridge_tbar_eq_frame
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    mixedBridgeTbar M m t ω j = mixedBridgeFrameTbar M m t ω j := by
  let Q := originCube 2 m
  have hm (f : TriadicCube 2 → ℝ) :
      Cold.squareCellMean Q j (fun C => f C.val) = descendantsAverage Q j f := by
    unfold Cold.squareCellMean descendantsAverage
    congr 1
    exact Finset.sum_attach (descendantsAtDepth Q j) f
  have havg : descendantsAverage Q j (fun U => rawCubeFourLoadTrace M m U t ω) =
      descendantsAverage Q j (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mixedBridgeResponseCoefficient m t ω)) 1) := by
    unfold descendantsAverage
    apply congrArg (fun z => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * z)
    apply Finset.sum_congr rfl
    intro U hU
    exact mixed_bridge_raw_cube_trace_eq_frame M m t ω ht j hU
  change Cold.squareCellMean Q j (fun C => rawCubeFourLoadTrace M m C.val t ω) =
    descendantsAverage Q j (fun U => traceDefect (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mixedBridgeResponseCoefficient m t ω)) 1)
  calc
    Cold.squareCellMean Q j (fun C => rawCubeFourLoadTrace M m C.val t ω) =
        descendantsAverage Q j (fun U => rawCubeFourLoadTrace M m U t ω) :=
      hm (fun U => rawCubeFourLoadTrace M m U t ω)
    _ = _ := havg

/-- The parent trace subtracted in the projection estimate is the same
sample-path trace used by the mixed-bridge reference mean. -/
theorem mixed_bridge_anchor_trace_eq_frame
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mixedBridgeAnchorTrace M m t ω = mixedBridgeFrameAnchorTrace M m t ω := by
  let Q := originCube 2 m
  have hQ : Q ∈ descendantsAtDepth Q 0 := by
    simp [Homogenization.descendantsAtDepth_zero]
  have h := mixed_bridge_raw_cube_trace_eq_frame M m t ω ht 0 hQ
  simpa [mixedBridgeAnchorTrace, mixedBridgeFrameAnchorTrace,
    rawCubeFourLoadTrace] using h

/-- At every weak depth, the actual four-load parent primal projection energy
is bounded by the depth inverse times the exact child-minus-parent trace gap. -/
theorem mixed_bridge_primal_projection_gap_at_depth
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    mixedBridgeVDepthSq M m t ω j ≤
      lemmaVInverseDepthMax (originCube 2 m)
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mixedBridgeResponseCoefficient m t ω)) j *
        (mixedBridgeFrameTbar M m t ω j -
          mixedBridgeFrameAnchorTrace M m t ω) := by
  simpa [mixedBridgeVDepthSq, mixedBridgeFrameTbar,
    mixedBridgeFrameAnchorTrace, mixedBridgeResponseCoefficient] using
    (old_signed_primal_projection_trace_gap (originCube 2 m) j M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1
      (mixedBridgeResponseCoefficient m t ω))

/-- The exact child-minus-parent primal projection gap using the exported
raw-trace source observable. -/
theorem mixed_bridge_primal_projection_raw_gap_at_depth
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (ht : t ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    mixedBridgeVDepthSq M m t ω j ≤
      lemmaVInverseDepthMax (originCube 2 m)
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mixedBridgeResponseCoefficient m t ω)) j *
        (mixedBridgeTbar M m t ω j -
          mixedBridgeAnchorTrace M m t ω) := by
  simpa only [mixed_bridge_tbar_eq_frame M m t ω ht j,
    mixed_bridge_anchor_trace_eq_frame M m t ω ht] using
    mixed_bridge_primal_projection_gap_at_depth M m t ω j

/-- The actual parent primal and reciprocal weak profiles, kept paired, cost
two complete OLD-frame trace proxies. -/
theorem mixed_bridge_parent_pair_trace_proxy
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    mixedBridgeV2 M m t ω + mixedBridge M m t ω ≤
      2 * rawWeakTraceProxy
        (lemmaVInverseDepthMax (originCube 2 m)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mixedBridgeResponseCoefficient m t ω)))
        (mixedBridgeFrameTbar M m t ω) := by
  let Q := originCube 2 m
  let k := mixedBridgeResponseCoefficient m t ω
  let σ : ℝ := Annealed.sigmaBar M m
  change oldSignedPrimalErrorSize Q Q M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k ^ 2 +
      oldSignedReciprocalErrorSize Q Q M.nu σ M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 k ^ 2 ≤
    2 * rawWeakTraceProxy
      (lemmaVInverseDepthMax Q (responseFramePlanarCoefficientField M.nu σ k))
      (fun j => descendantsAverage Q j (fun U =>
        traceDefect (openCubeSet U)
          (responseFramePlanarCoefficientField M.nu σ k) 1))
  exact old_signed_parent_paired_weak_bound Q M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k

/-- The paired parent V/G weak bound now uses the exact raw `T̄` observable
exported for the source-history consumers. -/
theorem mixed_bridge_parent_pair_raw_trace_proxy
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mixedBridgeV2 M m t ω + mixedBridge M m t ω ≤
      2 * rawWeakTraceProxy
        (lemmaVInverseDepthMax (originCube 2 m)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mixedBridgeResponseCoefficient m t ω)))
        (mixedBridgeTbar M m t ω) := by
  have hseq : (fun j => mixedBridgeFrameTbar M m t ω j) =
      (fun j => mixedBridgeTbar M m t ω j) := by
    funext j
    exact (mixed_bridge_tbar_eq_frame M m t ω ht j).symm
  simpa only [hseq] using mixed_bridge_parent_pair_trace_proxy M m t ω

end
end ASDExplicitGamma.Inverse
