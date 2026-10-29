module

public import ASDExplicitGamma.Cold.PositiveTraceNorm
public import ASDExplicitGamma.Main.MultiplierMatrixBound
public import ASDExplicitGamma.Native.ParentBoundaryBandMatrix
public import ASDExplicitGamma.Native.GenericSourceBankAdapter

/-! Physical full-response operator control for the UPPER RESET step. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory Variational Native Inverse Algsuperdiff.Section3
open scoped RealInnerProductSpace
noncomputable section

/-- A positive physical coarse response operator is bounded by its full
four-load trace, with both symmetry and positivity proved from ellipticity. -/
theorem upper_cell_reset_operator_le_trace
    (Q : TriadicCube 2) {nu Lam : ℝ} {a : CoeffField 2}
    (hnu : 0 < nu) (hEll : IsEllipticFieldOn nu Lam (cubeSet Q) a) :
    fullResponseOperatorNorm Q a ≤ Matrix.trace (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a)) := by
  let A := toFullBlockMat (coarseBlockMatrix (cubeSet Q) a)
  let H := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) A
  have hA : A.PosDef := coarseBlockMatrix_posDef hnu hEll
  have hsym : H.toLinearMap.IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  have hpos (x : EuclideanSpace ℝ (BlockCoord 2)) : 0 ≤ inner ℝ x (H x) := by
    have hp := hA.posSemidef.dotProduct_mulVec_nonneg x.ofLp
    change 0 ≤ inner ℝ x (A.toEuclideanLin x)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply,star_trivial,dotProduct_comm] using hp
  have hn := Cold.norm_le_trace_of_positive_operator H hsym hpos
  have ht : LinearMap.trace ℝ (EuclideanSpace ℝ (BlockCoord 2)) H.toLinearMap=A.trace := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Cold.trace_toEuclideanLin]
  rw [ht] at hn
  rw [fullResponseOperatorNorm,Main.block_apply_opNorm_eq_full_matrix_opNorm]
  exact hn

/-- Every actual attenuated terminal coefficient uses the completed OLD
frame before its physical response is compared with the full bank trace. -/
theorem upper_cell_reset_normalized_operator_le_full_trace
    (M : ABKModel 2) (n J : ℤ) (weights : ℤ → ℝ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    fullResponseOperatorNorm Q
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • attenuatedCoefficient M n J weights ω) ≤
        nativeSourceFullResponseTrace M Q n J weights ω := by
  obtain ⟨Lam,_hLam,hEll⟩ := parent_boundary_band_elliptic_cube M n J weights ω Q
  have hs := (Annealed.sigmaBar_characterization M n).1
  have hn := upper_cell_reset_operator_le_trace Q
    (mul_pos (inv_pos.mpr hs) M.nu_pos) (Cold.cold_isEllipticFieldOn_smul (inv_pos.mpr hs) hEll)
  rw [Cold.cold_coarse_frame M.nu_pos hEll hs] at hn
  exact hn

/-- The actual OLD-frame full coarse matrix has measurable entries before
any operator norm or descendant maximum is taken. -/
theorem upper_cell_reset_framed_matrix_measurable
    (M : ABKModel 2) (n J : ℤ) (weights : ℤ → ℝ) (Q : TriadicCube 2) :
    Measurable (fun ω : Cutoff.CutoffSample 2 => toFullBlockMat
      (frameMatrix (Annealed.sigmaBar M n) (coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M n J weights ω)))) := by
  have hm := parent_boundary_band_full_coarse_measurable M n J weights Q
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact ((hm.eval_matrix (i := .inl i) (j := .inl j)).const_mul _)
    | inr j => exact hm.eval_matrix (i := .inl i) (j := .inr j)
  | inr i =>
    cases j with
    | inl j => exact hm.eval_matrix (i := .inr i) (j := .inl j)
    | inr j => exact ((hm.eval_matrix (i := .inr i) (j := .inr j)).const_mul _)

/-- The literal physical full-response operator norm is measurable. No
measurability or stochastic bound is assumed on the export. -/
theorem upper_cell_reset_normalized_operator_measurable
    (M : ABKModel 2) (n J : ℤ) (weights : ℤ → ℝ) (Q : TriadicCube 2) :
    Measurable (fun ω : Cutoff.CutoffSample 2 => fullResponseOperatorNorm Q
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • attenuatedCoefficient M n J weights ω)) := by
  have heq (ω) : fullResponseOperatorNorm Q
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • attenuatedCoefficient M n J weights ω)=
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)
        (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n)
          (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M n J weights ω))))‖ := by
    obtain ⟨Lam,_hLam,hEll⟩ := parent_boundary_band_elliptic_cube M n J weights ω Q
    rw [fullResponseOperatorNorm,Cold.cold_coarse_frame M.nu_pos hEll
      (Annealed.sigmaBar_characterization M n).1,Main.block_apply_opNorm_eq_full_matrix_opNorm]
  simp_rw [heq]
  have hc := ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2 )).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).norm
  exact hc.measurable.comp (upper_cell_reset_framed_matrix_measurable M n J weights Q)

end
end ASDExplicitGamma.Scalar
