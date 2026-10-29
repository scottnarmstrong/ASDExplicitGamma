module

public import ASDExplicitGamma.Native.GenericSourceBandCoefficientW
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw

public import ASDExplicitGamma.Native.NativeBandWeight

/-! Exact descendant frame matrices on the simultaneous source band. The
restriction helpers are adapted from PureFluxGeneratorBankLaw. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
noncomputable section

variable {W : NativeAmp}

local instance sourceBandFrameCompact (P : TriadicCube 2) :
    CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure

private noncomputable def sourceBandClosedCubeInclusion_W (W : NativeAmp) {P R : TriadicCube 2}
    {d : ℕ} (hR : R ∈ descendantsAtDepth P d) :
    C(closure (cubeSet R), closure (cubeSet P)) :=
  ⟨fun x => ⟨x.1, closure_mono (cubeSet_subset_of_mem_descendantsAtDepth hR) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

private noncomputable def sourceBandResponseCoefficientOnDescendant_W (W : NativeAmp)
    {P R : TriadicCube 2} {d : ℕ} (hR : R ∈ descendantsAtDepth P d) :
    C(closure (cubeSet P), ℝ) →L[ℝ] ResponseCoefficient (cubeSet R) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    (sourceBandClosedCubeInclusion_W W hR)).comp
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closure (cubeSet P)) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

private theorem sourceBandResponseCoefficientOnDescendant_extension_W
    {P R : TriadicCube 2} {d : ℕ}
    (hR : R ∈ descendantsAtDepth P d)
    (f : C(closure (cubeSet P), ℝ)) {x : Vec 2} (hx : x ∈ cubeSet R) :
    responseCoefficientExtension (sourceBandResponseCoefficientOnDescendant_W W hR f) x =
      f ⟨x, subset_closure ((cubeSet_subset_of_mem_descendantsAtDepth hR) hx)⟩ := by
  rw [responseCoefficientExtension_eq _ hx]
  simp [sourceBandResponseCoefficientOnDescendant_W,
    sourceBandClosedCubeInclusion_W,
    BoundedContinuousFunction.compContinuousCLM_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]

/-- Every descendant matrix of the normalized simultaneous source scalar
is the actual physical bank matrix in the true completed frame. -/
theorem native_source_band_coarse_matrix_frame_W
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    {R : TriadicCube 2} {d : ℕ} (hR : R ∈ descendantsAtDepth (originCube 2 n) d) :
    coarseBlockMatrix (cubeSet R)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (pureFluxOpenResponseRestriction n (nativeSourceBandScalar_W W n height t ω))) =
      frameMatrix (Annealed.sigmaBar M n:ℝ)
        (coarseBlockMatrix (cubeSet R)
          (attenuatedCoefficient M n (n+(height:ℤ)) (nativeAttW W t) ω)) := by
  let P := originCube 2 n
  let f := nativeSourceBandScalar_W W n height t ω
  let k := sourceBandResponseCoefficientOnDescendant_W W hR f
  let σ : ℝ := Annealed.sigmaBar M n
  have hσ := (Annealed.sigmaBar_characterization M n).1
  have hsource (x : Vec 2) (hx : x ∈ openCubeSet R) :
      responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction n f) x =
        responseFramePlanarCoefficientField M.nu σ k x := by
    change responsePlanarCoefficient (M.nu/σ)
        (responseCoefficientExtension (pureFluxOpenResponseRestriction n f) x/σ)=
      responsePlanarCoefficient (M.nu/σ) (responseCoefficientExtension k x/σ)
    rw [pureFluxOpenResponseRestriction_value n f
      (openCubeSet_subset_of_mem_descendantsAtDepth hR hx),
      sourceBandResponseCoefficientOnDescendant_extension_W hR f (openCubeSet_subset_cubeSet R hx)]
  have hframe : coarseBlockMatrix (cubeSet R)
      (responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction n f)) =
      coarseBlockMatrix (cubeSet R) (responseFramePlanarCoefficientField M.nu σ k) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hsource x hx
  have hphysical (x : Vec 2) (hx : x ∈ openCubeSet R) :
      responsePlanarCoefficientField M.nu k x =
        attenuatedCoefficient M n (n+(height:ℤ)) (nativeAttW W t) ω x := by
    change responsePlanarCoefficient M.nu (responseCoefficientExtension k x)=_
    rw [sourceBandResponseCoefficientOnDescendant_extension_W hR f (openCubeSet_subset_cubeSet R hx)]
    have hxP := (cubeSet_subset_of_mem_descendantsAtDepth hR) (openCubeSet_subset_cubeSet R hx)
    have hh := native_source_band_coefficient_on_cube_W (W := W) M n height t ω x hxP
    rw [responsePlanarCoefficientField,responseCoefficientExtension_eq _ hxP,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply] at hh
    exact hh
  have hphysicalMatrix : coarseBlockMatrix (cubeSet R) (responsePlanarCoefficientField M.nu k) =
      coarseBlockMatrix (cubeSet R)
        (attenuatedCoefficient M n (n+(height:ℤ)) (nativeAttW W t) ω) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hphysical x hx
  calc
    _ = coarseBlockMatrix (cubeSet R) (responseFramePlanarCoefficientField M.nu σ k) := hframe
    _ = frameMatrix σ (coarseBlockMatrix (cubeSet R) (responsePlanarCoefficientField M.nu k)) :=
      response_coarseMatrix_frame_eq (measurableSet_cubeSet R) M.nu σ M.nu_pos hσ k
    _ = _ := by rw [hphysicalMatrix]

end
end ASDExplicitGamma.Native
