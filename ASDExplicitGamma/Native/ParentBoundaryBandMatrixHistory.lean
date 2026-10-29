module

public import ASDExplicitGamma.Native.OldSignedMatrixHistoryControl
public import ASDExplicitGamma.Native.ParentBoundaryBandDirectionalFrame

/-! Matrix-history control in the exact physical OLD display field. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The source descendant matrix is also the coarse matrix of the physical
coefficient divided by its fixed completed frame. -/
theorem parent_boundary_band_normalized_matrix (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ)
    (V : TriadicCube 2) (hV : V ∈ descendantsAtDepth U j) :
    coarseBlockMatrix (openCubeSet V) (parentBoundaryBandFrameField M n height t ω)=
      coarseBlockMatrix (cubeSet V) ((Annealed.sigmaBar M n : ℝ)⁻¹ •
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)) := by
  rw [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V]
  dsimp only [parentBoundaryBandFrameField]
  rw [native_source_band_coarse_matrix_frame M n height t ω (mem_descendantsAtDepth_add hU hV)]
  obtain ⟨Lam,_hLam,hEll⟩ := parent_boundary_band_elliptic_cube M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) ω V
  exact (Cold.cold_coarse_frame M.nu_pos hEll (Annealed.sigmaBar_characterization M n).1).symm

/-- Each actual local depth maximum obeys the sharp scalar matrix bound. -/
theorem parent_boundary_band_response_depth_le_max_trace (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    let a := parentBoundaryBandFrameField M n height t ω
    fullResponseDepthMax U a j ≤ 1+2*oldSignedMaxTraceDepth U a j+
      Real.sqrt (2*oldSignedMaxTraceDepth U a j) := by
  intro a
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty U j)
  intro V hV
  have hmatrix := parent_boundary_band_normalized_matrix M n height r U hU t ω j V hV
  have hnorm : fullResponseOperatorNorm V a=fullResponseOperatorNorm V
      ((Annealed.sigmaBar M n : ℝ)⁻¹ • (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)) := by
    unfold fullResponseOperatorNorm
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V a,hmatrix]
  obtain ⟨Lam,_hLam,hEll⟩ := parent_boundary_band_elliptic_cube M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) ω V
  have hnormalized := Cold.cold_isEllipticFieldOn_smul
    (inv_pos.mpr (Annealed.sigmaBar_characterization M n).1) hEll
  have hb := Main.main_full_response_operator_norm_le_trace_bound V
    (mul_pos (inv_pos.mpr (Annealed.sigmaBar_characterization M n).1) M.nu_pos) hnormalized
  have htrace : traceDefect (cubeSet V) ((Annealed.sigmaBar M n:ℝ)⁻¹ •
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω) 1=
      traceDefect (openCubeSet V) a 1 := by
    unfold traceDefect
    rw [←hmatrix]
  rw [←hnorm,htrace] at hb
  have hmax : traceDefect (openCubeSet V) a 1≤oldSignedMaxTraceDepth U a j :=
    le_csSup (((Set.toFinite _).image _).bddAbove) ⟨V,hV,rfl⟩
  have h2 := mul_le_mul_of_nonneg_left hmax (by norm_num : (0:ℝ)≤2)
  exact hb.trans (add_le_add (add_le_add le_rfl h2) (Real.sqrt_le_sqrt h2))

/-- Actual response and corrector histories are controlled by the same
maximum trace history, with all series finite by actual ellipticity. -/
theorem parent_boundary_band_matrix_history_bounds (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    let a := parentBoundaryBandFrameField M n height t ω
    let H := oldSignedMaxTraceHistory U a
    oldSignedResponseHistory U a ≤ 1+2*H+Real.sqrt (2*H) ∧
      oldSignedCorrectorHistory U a ≤ (1+inverseHistoryDiscount)*(1+2*H+Real.sqrt (2*H))*H := by
  intro a H
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hM : oldSignedResponseHistory U a ≤ 1+2*H+Real.sqrt (2*H) := by
    rw [(old_signed_response_history_series U a hEll).2]
    exact Main.main_weighted_matrix_history_bound inverseHistoryDiscount
      inverse_history_discount_range.1.le inverse_history_discount_range.2
      (fullResponseDepthMax U a) (oldSignedMaxTraceDepth U a)
      (fun j => (old_signed_max_trace_depth_bounds U a hEll j).1)
      (fun j => ⟨full_response_depth_max_nonneg U a j,
        parent_boundary_band_response_depth_le_max_trace M n height r U hU t ω j⟩)
      (old_signed_max_trace_series_summable U a hEll)
  have hT := old_signed_trace_history_le_max_trace U a hEll
  have hM0 : 0≤oldSignedResponseHistory U a := ENNReal.toReal_nonneg
  have hD : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  exact ⟨hM,mul_le_mul (mul_le_mul_of_nonneg_left hM hD) hT ENNReal.toReal_nonneg
    (mul_nonneg hD (hM0.trans hM))⟩

end
end ASDExplicitGamma.Native
