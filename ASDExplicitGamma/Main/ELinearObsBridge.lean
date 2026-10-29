module

public import ASDExplicitGamma.Main.ELinearHistoryBridge
public import ASDExplicitGamma.Main.AffineObserverFrame

/-! Observer-root bridge: for an arbitrary observer root `Q` and insertion
label `m`, the frame field of the partial-insertion coefficient on `Q` agrees
on every descendant cell with the cell's own frame field. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff
attribute [local irreducible] Homogenization.descendantsAtDepth

local instance eLinearObsCubeCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

theorem old_signed_obs_frame_eq_scaled_partial
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (x : Vec 2) (hx : x ∈ openCubeSet Q) :
    oldSignedPartialFrameFieldAt M Q m t ω x =
      (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x := by
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact (closure (cubeSet Q))
    (isBounded_cubeSet Q).isCompact_closure
  let xK : closure (cubeSet Q) := ⟨x, subset_closure (openCubeSet_subset_cubeSet Q hx)⟩
  have hscalar := Gaussian.modelInsertedScalar_apply (closure (cubeSet Q)) M ell m hK t ω xK
  have hv : responseCoefficientExtension (mainAffineOpenResponseRestriction Q
      (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω)) x =
      (Model.partialInsertedCoefficient M m t ω).toFun x 1 0 := by
    rw [main_affine_open_response_restriction_value Q _ hx]
    simpa [xK] using hscalar
  have hσ : (0:ℝ) < Annealed.sigmaBar M m := (Annealed.sigmaBar_characterization M m).1
  have hsym := main_partial_inserted_symmPart M m t ω x
  have hp := planar_coefficient_eq_of_symmPart M.nu _ hsym
  change responsePlanarCoefficient (M.nu / (Annealed.sigmaBar M m : ℝ))
      (responseCoefficientExtension (mainAffineOpenResponseRestriction Q
        (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω)) x / _) = _
  rw [hv]
  rw [← hp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ, Matrix.smul_apply] <;>
    field_simp [ne_of_gt hσ]

/-- Observer-root frame field and cell frame field agree a.e. on the cell. -/
theorem main_e_linear_obs_frame_ae
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (U : TriadicCube 2) (hsub : openCubeSet U ⊆ openCubeSet Q) :
    oldSignedPartialFrameFieldAt M Q m t ω =ᵐ[volumeMeasureOn (openCubeSet U)]
      responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t U ω) := by
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
  rw [old_signed_obs_frame_eq_scaled_partial M Q m t ω x (hsub hx),
    main_eosc_response_frame_eq_scaled_partial M m t U ω x hx]

/-- The inverse, response and corrector histories of a cell, from the
observer-root frame field. -/
theorem main_e_linear_obs_histories_bridge
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (U : TriadicCube 2) (hsub : openCubeSet U ⊆ openCubeSet Q) :
    oldSignedInverseHistory U (oldSignedPartialFrameFieldAt M Q m t ω) =
        oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) ∧
      oldSignedResponseHistory U (oldSignedPartialFrameFieldAt M Q m t ω) =
        oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) ∧
      oldSignedCorrectorHistory U (oldSignedPartialFrameFieldAt M Q m t ω) =
        oldSignedCorrectorHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) := by
  have hEllQ := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (mainAffineOpenResponseRestriction Q
      (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω))
  have hEllU := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (mainInsertionSkewCoefficient m t U ω)
  exact old_signed_histories_congr U _ _ (hEllQ.mono (measurableSet_openCubeSet U) hsub)
    hEllU (main_e_linear_obs_frame_ae M Q m t ω U hsub)

/-- The directional proxy of a cell is the proxy of its own frame field. -/
theorem main_e_linear_obs_proxy_bridge
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (U : TriadicCube 2) (hsub : openCubeSet U ⊆ openCubeSet Q) (e : Vec 2) :
    oldSignedDirectionalProxy U (oldSignedPartialFrameFieldAt M Q m t ω) e =
      oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) e := by
  have hEllQ := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (mainAffineOpenResponseRestriction Q
      (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω))
  have hEllU := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (mainInsertionSkewCoefficient m t U ω)
  exact old_signed_directional_proxy_congr U _ _ (hEllQ.mono (measurableSet_openCubeSet U) hsub)
    hEllU (main_e_linear_obs_frame_ae M Q m t ω U hsub) e

end ASDExplicitGamma.Main
