module

public import ASDExplicitGamma.Native.ParentHistoryBank
public import ASDExplicitGamma.Gaussian.FixedNuPositive

/-! Coarse Young comparison used only to prove genuine centered-history moments. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Physical trace on a descendant equals the trace in the one normalized
physical frame on the parent square. -/
theorem parent_history_physical_cell_trace
    (M : ABKModel 2) {P Q : TriadicCube 2} {j : ℕ} (hQ : Q∈descendantsAtDepth P j)
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    traceDefect (cubeSet Q) (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)
      (Annealed.sigmaBar M n)=traceDefect (openCubeSet Q) (parentHistoryPhysicalFrame M P n height t ω) 1 := by
  have hm := parent_boundary_common_cube_band_coarse_frame M P n height t ω
    (Annealed.sigmaBar M n) (Annealed.sigmaBar_characterization M n).1 hQ
  have hm' : coarseBlockMatrix (openCubeSet Q) (parentHistoryPhysicalFrame M P n height t ω)=
      frameMatrix (Annealed.sigmaBar M n) (coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)) := by
    rw [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q]
    exact hm
  unfold traceDefect
  rw [hm']
  simp only [frameMatrix,Matrix.trace_smul,smul_eq_mul,inv_one,one_mul]

/-- The fixed positive symmetric part bounds every actual inverse block
uniformly in depth; this coarse bound is used for moments only. -/
theorem parent_history_cell_inverse_trace_bound
    (M : ABKModel 2) {P Q : TriadicCube 2} {j : ℕ} (hQ : Q∈descendantsAtDepth P j)
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    Matrix.trace (frameMatrix (Annealed.sigmaBar M n) (coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω))).lowerRight ≤
        2*((Annealed.sigmaBar M n:ℝ)/M.nu) := by
  let sigma : ℝ := Annealed.sigmaBar M n
  let k := parentBoundaryCellCoefficient hQ (parentBoundaryCommonCubeBand P n height t ω)
  let B := (coarseBlockMatrix (cubeSet Q) (responseFramePlanarCoefficientField M.nu sigma k)).lowerRight
  have hsigma := (Annealed.sigmaBar_characterization M n).1
  have he : frameMatrix sigma (coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω))=
      coarseBlockMatrix (cubeSet Q) (responseFramePlanarCoefficientField M.nu sigma k) := by
    rw [←parent_boundary_common_cell_physical_coarse M hQ]
    exact (response_coarseMatrix_frame_eq (measurableSet_cubeSet Q) M.nu sigma M.nu_pos hsigma k).symm
  rw [he]
  have hnorm := fixedNu_inverse_norm_le Q M.nu sigma M.nu_pos hsigma k
  have h0 : B 0 0 ≤ Book.Ch02.matrixNorm B := by
    exact (le_abs_self _).trans (by simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
      Book.Ch02.matrixOperatorNorm] using clipped_matrix_entry_abs_le_norm B 0 0)
  have h1 : B 1 1 ≤ Book.Ch02.matrixNorm B := by
    exact (le_abs_self _).trans (by simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
      Book.Ch02.matrixOperatorNorm] using clipped_matrix_entry_abs_le_norm B 1 1)
  have htrace : Matrix.trace B ≤ 2*Book.Ch02.matrixNorm B := by
    simp only [Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply]
    linarith only [h0,h1]
  exact htrace.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))

/-- Coarse centered versus physical depth maxima, with a depth-independent
Gaussian-square correction. Every spatial maximum is the actual one. -/
theorem parent_history_centered_depth_young
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    oldSignedMaxTraceDepth P (parentHistoryCenteredFrame M P n height t ω) j ≤
      2*oldSignedMaxTraceDepth P (parentHistoryPhysicalFrame M P n height t ω) j+4+
        4*(parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ))^2*
          ((Annealed.sigmaBar M n:ℝ)/M.nu) := by
  classical
  unfold oldSignedMaxTraceDepth
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty P j)
  intro Q hQ
  have hy := parent_boundary_common_cube_full_young M hQ n height t ω 1 (by norm_num)
  dsimp only at hy
  rw [parent_history_centered_cell_trace] at hy
  rw [parent_boundary_common_physical_full_eq,parent_history_physical_cell_trace M hQ] at hy
  have hd := parent_history_cell_inverse_trace_bound M hQ n height t ω
  have hpaid := mul_le_mul_of_nonneg_left hd
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg (parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ))))
  have hmax : traceDefect (openCubeSet Q) (parentHistoryPhysicalFrame M P n height t ω) 1 ≤
      Book.Ch02.finsetSupReal (descendantsAtDepth P j) (fun R =>
        traceDefect (openCubeSet R) (parentHistoryPhysicalFrame M P n height t ω) 1) :=
    le_csSup ((Set.toFinite _).image _).bddAbove ⟨Q,hQ,rfl⟩
  norm_num at hy
  linarith only [hy,hpaid,hmax]

end
end ASDExplicitGamma.Native
