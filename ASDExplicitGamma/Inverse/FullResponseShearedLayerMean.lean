module

public import ASDExplicitGamma.Inverse.AssemblyShearedMean
public import ASDExplicitGamma.Inverse.FullResponseIdentityShear

/-! Full-row sheared means using the generic trace and physical-shear API. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- The complete actual clipped trace on a deterministic sheared layer. -/
def fullResponseShearedLayerTrace (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ U ∈ whitneyRootLayer Q H i,
    ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*
      (Matrix.trace ((assemblyPhysicalShearMatrix M (U.scale+40) U.scale N
          (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale)
          (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights ω).transpose*
        clippedCellMatrix M (U.scale+40) U (rootTau .full) ω*
          assemblyPhysicalShearMatrix M (U.scale+40) U.scale N
          (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale)
          (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights ω)/4)

/-- The protected actual old mean gives exactly μ(v+half the squared shear),
plus the norm of the actual centered matrix. No random mask is conditioned on. -/
theorem full_response_sheared_layer_mean_bound (M : ABKModel 2) (h : ℝ)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (H : ℕ)
    (hH : 377 ≤ H)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342 → nativeInductionState M h n)
    (i : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    fullResponseShearedLayerTrace M Q H (i+1) N weights ω ≤
      (29/25:ℝ)*(bankLayerWeight i+assemblyLayerMeanSquare M Q H (i+1) N weights ω/2)+
        ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
          (assemblyShearedCenteredLayerMatrix M Q H (i+1) (rootTau .full) N weights ω)‖ := by
  classical
  let s := whitneyRootLayer Q H (i+1)
  let w := fun U : TriadicCube 2 => (volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal
  let R := fun U : TriadicCube 2 => assemblyPhysicalShearMatrix M (U.scale+40) U.scale N
    (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale) (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights ω
  let Y := fun U : TriadicCube 2 => clippedCellMatrix M (U.scale+40) U (rootTau .full) ω
  let E := fun U : TriadicCube 2 => ∫ ζ, clippedCellMatrix M (U.scale+40) U (rootTau .full) ζ
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have hw (U : TriadicCube 2) : 0 ≤ w U := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hmean (U : TriadicCube 2) (hU : U ∈ s) :
      Matrix.trace ((R U).transpose*E U*R U)/4 ≤
        (29/25:ℝ)*(Matrix.trace ((R U).transpose*R U)/4) := by
    have hstate : nativeInductionState M h (U.scale+40) := hpast _ (by
      have hs := root_whitney_layer_scale Q H (i+1) hU
      unfold whitneyProfile at hs
      omega)
    obtain ⟨_,hbuf,_,_⟩ := reset_native_coordinates M h (U.scale+40) hstate
    apply assembly_trace_le_of_quadratic
    intro v
    rw [fullMatrixQuadratic_congruence,fullMatrixQuadratic_shear_metric]
    exact clipped_cell_matrix_mean_le M (U.scale+40) U (by omega)
      M.shellPrefix.gamma_pos hγ hbuf (rootTau .full) ((R U).mulVec v)
  have hmeans := Finset.sum_le_sum (fun U (hU : U ∈ s) =>
    mul_le_mul_of_nonneg_left (hmean U hU) (hw U))
  have hsplit : fullResponseShearedLayerTrace M Q H (i+1) N weights ω =
      Matrix.trace (assemblyShearedCenteredLayerMatrix M Q H (i+1) (rootTau .full) N weights ω)/4+
        ∑ U ∈ s, w U*(Matrix.trace ((R U).transpose*E U*R U)/4) := by
    have hmat (U : TriadicCube 2) : (R U).transpose*(Y U-E U)*R U =
        (R U).transpose*Y U*R U-(R U).transpose*E U*R U := by noncomm_ring
    change (∑ U ∈ s, w U*(Matrix.trace ((R U).transpose*Y U*R U)/4)) =
      Matrix.trace (∑ U ∈ s, w U • ((R U).transpose*(Y U-E U)*R U))/4+
        ∑ U ∈ s, w U*(Matrix.trace ((R U).transpose*E U*R U)/4)
    simp_rw [hmat]
    simp only [Matrix.trace_sum,Matrix.trace_smul,Matrix.trace_sub,Finset.sum_div]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro U hU
    ring
  have hmetric : (∑ U ∈ s, w U*((29/25:ℝ)*(Matrix.trace ((R U).transpose*R U)/4))) =
      (29/25:ℝ)*(bankLayerWeight i+assemblyLayerMeanSquare M Q H (i+1) N weights ω/2) := by
    simp_rw [R,assemblyPhysicalShearMatrix,assembly_shear_metric_trace]
    let g := fun U : TriadicCube 2 => physicalMissingWaveAverage M (U.scale+40) U.scale N
      (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale) (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale)
        weights ω/Annealed.sigmaBar M (U.scale+40)
    change (∑ U ∈ s, w U*((29/25:ℝ)*(1+(g U)^2/2))) = _
    calc
      _ = ∑ U ∈ s, (29/25:ℝ)*(w U+w U*(g U)^2/2) := by
        apply Finset.sum_congr rfl
        intro U hU
        ring
      _ = (29/25:ℝ)*((∑ U ∈ s, w U)+(∑ U ∈ s, w U*(g U)^2)/2) := by
        rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_div]
      _ = _ := by
        rw [show ∑ U ∈ s, w U=bankLayerWeight i from root_matrix_layer_weights_sum Q H i]
        rfl
  have hcenter := (le_abs_self (Matrix.trace
    (assemblyShearedCenteredLayerMatrix M Q H (i+1) (rootTau .full) N weights ω)/4)).trans
      (full_block_normalized_trace_abs_le_euclidean_opNorm _)
  rw [hsplit]
  rw [hmetric] at hmeans
  exact add_le_add hcenter hmeans |>.trans_eq (by ring)

end
end ASDExplicitGamma.Inverse
