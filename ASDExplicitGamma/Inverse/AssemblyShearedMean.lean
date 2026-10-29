module

public import ASDExplicitGamma.Inverse.AssemblyShearedLayers
public import ASDExplicitGamma.Inverse.AssemblyLayerComparison
public import ASDExplicitGamma.Inverse.FullResponseMatrixError

/-! Exact sheared clipped-layer means and their actual centered errors. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Quadratic domination controls the normalized full trace without dimension loss. -/
theorem assembly_trace_le_of_quadratic (A B : FullBlockMat 2) (c : ℝ)
    (hAB : ∀ v : BlockCoord 2 → ℝ, fullMatrixQuadratic v A ≤ c*fullMatrixQuadratic v B) :
    Matrix.trace A/4 ≤ c*(Matrix.trace B/4) := by
  have hd (i : BlockCoord 2) : A i i ≤ c*B i i := by
    have hh := hAB (Pi.single i 1)
    change dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) ≤
      c*dotProduct (Pi.single i 1) (B.mulVec (Pi.single i 1)) at hh
    simpa only [single_dotProduct,one_mul,Matrix.mulVec_single_one,Matrix.col_apply] using hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hd i)
  change Matrix.trace A ≤ ∑ i : BlockCoord 2, c*B i i at hs
  rw [← Finset.mul_sum] at hs
  have hh := div_le_div_of_nonneg_right hs (by norm_num : (0:ℝ) ≤ 4)
  exact hh.trans_eq (by simp only [Matrix.trace,Matrix.diag_apply]; ring)

/-- The squared Hilbert-Schmidt norm of a planar stream shear is exact. -/
theorem assembly_shear_metric_trace (g : ℝ) :
    Matrix.trace ((constantSkewMatrix g).transpose*constantSkewMatrix g)/4 = 1+g^2/2 := by
  simp [constantSkewMatrix,toFullBlockMat,Response.responsePlanarJ,Matrix.trace,
    Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type,Fin.sum_univ_two]
  ring

/-- The complete actual clipped trace on a deterministic sheared layer. -/
def assemblyShearedLayerTrace (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ U ∈ whitneyRootLayer Q H i,
    ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*
      (Matrix.trace ((assemblyPhysicalShearMatrix M (U.scale+40) U.scale N
          (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale)
          (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights ω).transpose*
        clippedCellMatrix M (U.scale+40) U resetAllOrderTau ω*
          assemblyPhysicalShearMatrix M (U.scale+40) U.scale N
          (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale)
          (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights ω)/4)

/-- The complete physical squared-average shear payment on the same layer. -/
def assemblyLayerMeanSquare (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ U ∈ whitneyRootLayer Q H i,
    ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*
      (physicalMissingWaveAverage M (U.scale+40) U.scale N
        (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale)
        (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights ω/Annealed.sigmaBar M (U.scale+40))^2

/-- The protected actual old mean gives exactly μ(v+half the squared shear),
plus the norm of the actual centered matrix. No random mask is conditioned on. -/
theorem assembly_sheared_layer_mean_bound (M : ABKModel 2) (h : ℝ)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (k H : ℕ)
    (hH : heightEntrance k ≤ H)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (i : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    assemblyShearedLayerTrace M Q H (i+1) N weights ω ≤
      (29/25:ℝ)*(bankLayerWeight i+assemblyLayerMeanSquare M Q H (i+1) N weights ω/2)+
        ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
          (assemblyShearedCenteredLayerMatrix M Q H (i+1) resetAllOrderTau N weights ω)‖ := by
  classical
  let s := whitneyRootLayer Q H (i+1)
  let w := fun U : TriadicCube 2 => (volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal
  let R := fun U : TriadicCube 2 => assemblyPhysicalShearMatrix M (U.scale+40) U.scale N
    (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale) (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights ω
  let Y := fun U : TriadicCube 2 => clippedCellMatrix M (U.scale+40) U resetAllOrderTau ω
  let E := fun U : TriadicCube 2 => ∫ ζ, clippedCellMatrix M (U.scale+40) U resetAllOrderTau ζ
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have hw (U : TriadicCube 2) : 0 ≤ w U := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hmean (U : TriadicCube 2) (hU : U ∈ s) :
      Matrix.trace ((R U).transpose*E U*R U)/4 ≤
        (29/25:ℝ)*(Matrix.trace ((R U).transpose*R U)/4) := by
    have hlabel := root_whitney_old_cutoff_eq Q H (i+1) hU
    have hcut := layer_old_cutoff_le_protected Q.scale k H (i+1) hH (by omega)
    have hstate : nativeInductionState M h (U.scale+40) := hpast _ (by
      rw [← hlabel]
      simpa only [protectedOldLabel] using hcut)
    obtain ⟨_,hbuf,_,_⟩ := reset_native_coordinates M h (U.scale+40) hstate
    apply assembly_trace_le_of_quadratic
    intro v
    rw [fullMatrixQuadratic_congruence,fullMatrixQuadratic_shear_metric]
    exact clipped_cell_matrix_mean_le M (U.scale+40) U (by omega)
      M.shellPrefix.gamma_pos hγ hbuf resetAllOrderTau ((R U).mulVec v)
  have hmeans := Finset.sum_le_sum (fun U (hU : U ∈ s) =>
    mul_le_mul_of_nonneg_left (hmean U hU) (hw U))
  have hsplit : assemblyShearedLayerTrace M Q H (i+1) N weights ω =
      Matrix.trace (assemblyShearedCenteredLayerMatrix M Q H (i+1) resetAllOrderTau N weights ω)/4+
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
    (assemblyShearedCenteredLayerMatrix M Q H (i+1) resetAllOrderTau N weights ω)/4)).trans
      (full_block_normalized_trace_abs_le_euclidean_opNorm _)
  rw [hsplit]
  rw [hmetric] at hmeans
  exact add_le_add hcenter hmeans |>.trans_eq (by ring)

end
end ASDExplicitGamma.Inverse
