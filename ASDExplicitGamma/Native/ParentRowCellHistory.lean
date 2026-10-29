module

public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxy
public import ASDExplicitGamma.Native.GenericSourceBandHistory
public import ASDExplicitGamma.Native.ParentBoundaryBandMatrixHistory

/-! Actual simultaneous-band histories for every cell in the parent row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- Every comparison cell is controlled by the same finite simultaneous-band inverse history. -/
theorem parent_row_cell_inverse_history
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ k<n,nativeInductionState M h k) (r : ℕ) (hr : r≤5)
    (t : ℝ) (ht : t≤1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ U ∈ descendantsAtDepth (originCube 2 n) r,
      oldSignedInverseHistory U (parentBoundaryBandFrameField M n height t ω)≤
        (nativeSourceBandHistory M n height t ω).toReal := by
  have hb := native_source_band_local_bank M h hM hg n height hpast t ht
  filter_upwards [hb.history_finite] with ω hfinite
  intro U hU
  exact native_source_band_mesh_history_le M n height t ω r hr hfinite.ne hU

/-- The complete physical maximum trace history is nonnegative on each source cell. -/
theorem parent_row_cell_max_history_nonneg (M : ABKModel 2) (n : ℤ)
    (height r : ℕ) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    0≤oldSignedMaxTraceHistory U (parentBoundaryBandFrameField M n height t ω) := by
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  unfold oldSignedMaxTraceHistory
  apply mul_nonneg (sub_nonneg.mpr inverse_history_discount_range.2.le)
  exact tsum_nonneg (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le j)
    (old_signed_max_trace_depth_bounds U _ hEll j).1)

/-- Both literal flat directional proxies are nonnegative in the same parent display field. -/
theorem parent_row_cell_flat_proxy_nonneg (M : ABKModel 2) (n : ℤ)
    (height r : ℕ) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (t b : ℝ)
    (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) (plus : Bool) :
    0≤oldSignedFlatDirectionalMeanProxy (originCube 2 n) U
      (parentBoundaryBandFrameField M n height t ω) b L plus :=
  old_signed_flat_directional_proxy_nonneg _ _ (openCubeSet_subset_of_mem_descendantsAtDepth hU)
    M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)) b L plus

end
end ASDExplicitGamma.Native
