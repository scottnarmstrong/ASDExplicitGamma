module

public import ASDExplicitGamma.Native.ParentBoundaryBandInverseMeanCap
public import ASDExplicitGamma.Native.GenericSourceBandHistory
public import ASDExplicitGamma.Native.OldSignedHistoryMoments
public import ASDExplicitGamma.Inverse.RawShellBandBankInputs

/-! Exact total-bank payment of the physical inverse block on a simultaneous band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Gaussian Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The real simultaneous-band history has the total bank's exact second-moment cap. -/
theorem parent_row_band_history_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t≤1) :
    MemLp (fun ω => (nativeSourceBandHistory M n height t ω).toReal) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm (fun ω => (nativeSourceBandHistory M n height t ω).toReal) 2
      (Cutoff.cutoffSampleLaw M).toMeasure≤(3683/2500:ℝ) := by
  have h128 := raw_shell_weighted_local_history_L128 M h hM hg n (n+(height:ℤ))
    (by omega) (fun _ => Real.sqrt t)
    (fun _ _ => ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr ht⟩) hpast
  change eLpNorm (fun ω => (nativeSourceBandHistory M n height t ω).toReal) 128
    (Cutoff.cutoffSampleLaw M).toMeasure≤ENNReal.ofReal (3683/2500:ℝ) at h128
  have h2 := (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2:ℝ≥0∞)≤128)).trans h128
  refine ⟨lt_of_le_of_lt h2 ENNReal.ofReal_lt_top,?_⟩
  change (eLpNorm _ 2 _).toReal≤_
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h2).trans_eq
    (ENNReal.toReal_ofReal (by norm_num))

/-- The actual cell inverse mean is bounded by the total cap, without adding the rare reserve. -/
theorem parent_row_inverse_block_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height)
    (r : ℕ) (hr : r≤5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : t≤1) (hpast : ∀ k<n,nativeInductionState M h k) :
    parentBoundaryBandBlockMean M n height t U false≤(3683/2500:ℝ) := by
  let H := fun ω => (nativeSourceBandHistory M n height t ω).toReal
  let A := fun ω => parentBoundaryBandNormalizedBlock M n height t U false ω 0 0
  have hH := parent_row_band_history_L2 M h hM hg n height hpast t ht
  have hfirst := (old_signed_history_first_second_moments
    (Cutoff.cutoffSampleLaw M).toMeasure H (3683/2500) hH.1
    (fun _ => ENNReal.toReal_nonneg) (by norm_num) hH.2).1
  have hA : Integrable A (Cutoff.cutoffSampleLaw M).toMeasure :=
    (parent_boundary_band_block_scalar_law M h hM n height hheight r U hU t false).1 0 0
  have hb := native_source_band_local_bank M h hM hg n height hpast t ht
  have hle : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,A ω≤H ω := by
    filter_upwards [hb.history_finite] with ω hfinite
    have hEll := (responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1
      (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
    have hz := bank_inverse_depth_zero_le_history U _ hEll
      (show 1<(3:ℝ)^(1/4:ℝ) from Real.one_lt_rpow (by norm_num) (by norm_num))
    exact (parent_boundary_band_inverse_diagonal_le M n height r U hU t ω).trans
      (hz.trans (native_source_band_mesh_history_le M n height t ω r hr hfinite.ne hU))
  exact (integral_mono_ae hA (hH.1.integrable (by norm_num)) hle).trans hfirst

end
end ASDExplicitGamma.Native
