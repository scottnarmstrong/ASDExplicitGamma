module

public import ASDExplicitGamma.Gaussian.ModelHeatLaw
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Inverse.ResponseCoefficients
public import ASDExplicitGamma.Response.CoefficientFamily
public import ASDExplicitGamma.Variational.AdapterMu
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The actual partial insertion in the OLD response frame, restricted and
extended from an arbitrary observer root. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Inverse
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

noncomputable section

local instance affineObserverCubeCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- Inclusion of an open observer root's closure into its closed cube. -/
noncomputable def mainAffineOpenClosureInclusion (Q : TriadicCube 2) :
    C(closure (openCubeSet Q), closure (cubeSet Q)) := by
  exact ⟨fun x => ⟨x.1, closure_mono (openCubeSet_subset_cubeSet Q) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Restriction from the compact observer cube to its open response carrier. -/
noncomputable def mainAffineOpenResponseRestriction (Q : TriadicCube 2) :
    C(closure (cubeSet Q), ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    (mainAffineOpenClosureInclusion Q)).comp
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet Q)) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

/-- On the open observer root, the restriction-extension agrees with its
source continuous scalar. -/
theorem main_affine_open_response_restriction_value (Q : TriadicCube 2)
    (f : C(closure (cubeSet Q), ℝ)) {x : Vec 2}
    (hx : x ∈ openCubeSet Q) :
    responseCoefficientExtension (mainAffineOpenResponseRestriction Q f) x =
      f ⟨x, subset_closure (openCubeSet_subset_cubeSet Q hx)⟩ := by
  rw [responseCoefficientExtension_eq _ hx]
  simp [mainAffineOpenResponseRestriction, mainAffineOpenClosureInclusion,
    BoundedContinuousFunction.compContinuousCLM_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]

private noncomputable def mainAffineResponseCoefficientOnDescendant
    {P R : TriadicCube 2} {d : ℕ}
    (hR : R ∈ descendantsAtDepth P d) :
    C(closure (cubeSet P), ℝ) →L[ℝ] ResponseCoefficient (cubeSet R) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun x => ⟨x.1,
      closure_mono (cubeSet_subset_of_mem_descendantsAtDepth hR) x.2⟩,
      continuous_subtype_val.subtype_mk _⟩).comp
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closure (cubeSet P)) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

private theorem mainAffineResponseCoefficientOnDescendant_extension
    {P R : TriadicCube 2} {d : ℕ}
    (hR : R ∈ descendantsAtDepth P d)
    (f : C(closure (cubeSet P), ℝ)) {x : Vec 2} (hx : x ∈ cubeSet R) :
    responseCoefficientExtension
      (mainAffineResponseCoefficientOnDescendant hR f) x =
      f ⟨x, subset_closure ((cubeSet_subset_of_mem_descendantsAtDepth hR) hx)⟩ := by
  rw [responseCoefficientExtension_eq _ hx]
  simp [mainAffineResponseCoefficientOnDescendant,
    BoundedContinuousFunction.compContinuousCLM_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]

private theorem mainAffineSymmPartPartialInserted
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    Homogenization.symmPart (Model.partialInsertedCoefficient M m t ω x) =
      M.nu • (1 : Mat 2) := by
  have hsum (A B : Mat 2) : Homogenization.symmPart (A + B) =
      Homogenization.symmPart A + Homogenization.symmPart B := by
    ext i j
    simp only [Homogenization.symmPart, Matrix.add_apply]
    ring
  have hsmul (c : ℝ) (A : Mat 2) : Homogenization.symmPart (c • A) =
      c • Homogenization.symmPart A := by
    ext i j
    simp only [Homogenization.symmPart, Matrix.smul_apply]
    ring
  have hskew : Homogenization.symmPart
      (ShellField.forgetShell (ω.1 (m + 1)) x) = 0 := by
    ext i j
    change ((ω.1 (m + 1)) x i j + (ω.1 (m + 1)) x j i) / 2 = 0
    rw [(ω.1 (m + 1)).skew_entry x i j]
    ring
  change Homogenization.symmPart
    (Cutoff.coefficientCutoff M.nu m ω x +
      Real.sqrt t • ShellField.forgetShell (ω.1 (m + 1)) x) = _
  rw [hsum, hsmul, hskew, smul_zero, add_zero,
    Cutoff.symmPart_coefficientCutoff]

/-- The OLD-frame partial insertion rooted at an arbitrary observer cube.
The insertion scale `m` and deterministic response frame stay fixed as the
root changes. -/
noncomputable def oldSignedPartialFrameFieldAt
    (M : ABKModel 2) (Qroot : TriadicCube 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
  responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
    (mainAffineOpenResponseRestriction Qroot
      (Gaussian.modelInsertedScalar (closure (cubeSet Qroot)) m t ω))

/-- Every descendant cell of an observer root sees the actual partial
insertion in the fixed OLD frame. -/
theorem old_signed_partial_cell_frame_at
    (M : ABKModel 2) (Qroot : TriadicCube 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (U : TriadicCube 2) (j : ℕ)
    (hU : U ∈ descendantsAtDepth Qroot j) :
    coarseBlockMatrix (cubeSet U)
      (oldSignedPartialFrameFieldAt M Qroot m t ω) =
    frameMatrix (Annealed.sigmaBar M m : ℝ)
      (coarseBlockMatrix (cubeSet U)
        (Model.partialInsertedCoefficient M m t ω).toFun) := by
  let K : Set (Vec 2) := closure (cubeSet Qroot)
  let f := Gaussian.modelInsertedScalar K m t ω
  let hUcoeff := mainAffineResponseCoefficientOnDescendant hU f
  let σ := (Annealed.sigmaBar M m : ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hsource (x : Vec 2) (hx : x ∈ openCubeSet U) :
      responseFramePlanarCoefficientField M.nu σ
        (mainAffineOpenResponseRestriction Qroot f) x =
      responseFramePlanarCoefficientField M.nu σ hUcoeff x := by
    change responsePlanarCoefficient (M.nu / σ)
        (responseCoefficientExtension
          (mainAffineOpenResponseRestriction Qroot f) x / σ) =
      responsePlanarCoefficient (M.nu / σ)
        (responseCoefficientExtension hUcoeff x / σ)
    have hxRoot := openCubeSet_subset_of_mem_descendantsAtDepth hU hx
    rw [main_affine_open_response_restriction_value Qroot f hxRoot,
      mainAffineResponseCoefficientOnDescendant_extension hU f
        (openCubeSet_subset_cubeSet U hx)]
  have hframe :
      coarseBlockMatrix (cubeSet U)
        (responseFramePlanarCoefficientField M.nu σ
          (mainAffineOpenResponseRestriction Qroot f)) =
      coarseBlockMatrix (cubeSet U)
        (responseFramePlanarCoefficientField M.nu σ hUcoeff) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
    exact hsource x hx
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet Qroot).isCompact_closure
  have hphysical (x : Vec 2) (hx : x ∈ openCubeSet U) :
      responsePlanarCoefficientField M.nu hUcoeff x =
        (Model.partialInsertedCoefficient M m t ω).toFun x := by
    change responsePlanarCoefficient M.nu
      (responseCoefficientExtension hUcoeff x) = _
    rw [mainAffineResponseCoefficientOnDescendant_extension hU f
      (openCubeSet_subset_cubeSet U hx)]
    have hxRoot : x ∈ openCubeSet Qroot :=
      openCubeSet_subset_of_mem_descendantsAtDepth hU hx
    let xK : K := ⟨x, subset_closure (openCubeSet_subset_cubeSet Qroot hxRoot)⟩
    have hscalar := Gaussian.modelInsertedScalar_apply K M ell m hK t ω xK
    have hscalar' : f ⟨x, subset_closure
        ((cubeSet_subset_of_mem_descendantsAtDepth hU)
          (openCubeSet_subset_cubeSet U hx))⟩ =
        (Model.partialInsertedCoefficient M m t ω).toFun x 1 0 := by
      simpa [f, xK] using hscalar
    rw [hscalar']
    exact planar_coefficient_eq_of_symmPart M.nu _
      (mainAffineSymmPartPartialInserted M m t ω x)
  have hphysicalMatrix :
      coarseBlockMatrix (cubeSet U)
        (responsePlanarCoefficientField M.nu hUcoeff) =
      coarseBlockMatrix (cubeSet U)
        (Model.partialInsertedCoefficient M m t ω).toFun := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
    exact hphysical x hx
  calc
    coarseBlockMatrix (cubeSet U)
        (oldSignedPartialFrameFieldAt M Qroot m t ω) =
        coarseBlockMatrix (cubeSet U)
          (responseFramePlanarCoefficientField M.nu σ hUcoeff) := by
            simpa only [oldSignedPartialFrameFieldAt, K, f, σ] using hframe
    _ = frameMatrix σ
        (coarseBlockMatrix (cubeSet U) (responsePlanarCoefficientField M.nu hUcoeff)) :=
          response_coarseMatrix_frame_eq (measurableSet_cubeSet U) M.nu σ
            M.nu_pos hσ hUcoeff
    _ = frameMatrix σ
        (coarseBlockMatrix (cubeSet U)
          (Model.partialInsertedCoefficient M m t ω).toFun) := by
            rw [hphysicalMatrix]

end
end ASDExplicitGamma.Main

end
