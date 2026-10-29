module

public import ASDExplicitGamma.Inverse.AssemblyShearAlgebra

/-! The actual added-stream shear and its exact sign adapter to the estimates. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Variational
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section

/-- Reversing a constant skew has the same Euclidean operator norm. -/
theorem assembly_constant_skew_neg_norm (g : ℝ) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (constantSkewMatrix (-g))‖ =
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (constantSkewMatrix g)‖ := by
  let E : FullBlockMat 2 := Matrix.diagonal (Sum.elim (fun _ => (1:ℝ)) (fun _ => -1))
  have hE : ‖E‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    cases i <;> norm_num
  have he (a : ℝ) : constantSkewMatrix (-a) = E*constantSkewMatrix a*E := by
    ext α β
    cases α <;> cases β
    all_goals simp [E,constantSkewMatrix,toFullBlockMat,Matrix.diagonal_mul,Matrix.mul_diagonal]
  have hle (a : ℝ) : ‖constantSkewMatrix (-a)‖ ≤ ‖constantSkewMatrix a‖ := by
    rw [he a]
    calc
      _ ≤ ‖E‖*‖constantSkewMatrix a‖*‖E‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg E))
      _ ≤ 1*‖constantSkewMatrix a‖*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hE (norm_nonneg _)) hE
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [Matrix.l2_opNorm_toEuclideanCLM,Matrix.l2_opNorm_toEuclideanCLM]
  exact le_antisymm (hle g) (by simpa only [neg_neg] using hle (-g))

/-- The added-stream conjugator, with the sign of the variational load map. -/
def assemblyPhysicalShearMatrix (M : ABKModel 2) (j n N : ℤ) (a c : ℝ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : FullBlockMat 2 :=
  constantSkewMatrix (physicalMissingWaveAverage M j n N a c weights ω/Annealed.sigmaBar M j)

/-- The two sign conventions are related by an affine matrix map. -/
theorem assembly_physical_shear_sign (M : ABKModel 2) (j n N : ℤ) (a c : ℝ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    assemblyPhysicalShearMatrix M j n N a c weights ω =
      (2:ℝ) • (1:FullBlockMat 2)-physicalShearMatrix M j n N a c weights ω := by
  ext α β
  fin_cases α <;> fin_cases β <;>
    simp [assemblyPhysicalShearMatrix,physicalShearMatrix,constantSkewMatrix,
      toFullBlockMat,Response.responsePlanarJ] <;> ring

/-- The actual added-stream shear is ambient measurable. -/
theorem assembly_physical_shear_measurable (M : ABKModel 2) (j n N : ℤ) (a c : ℝ)
    (weights : ℤ → ℝ) : Measurable (assemblyPhysicalShearMatrix M j n N a c weights) := by
  have he : assemblyPhysicalShearMatrix M j n N a c weights =
      fun ω => (2:ℝ) • (1:FullBlockMat 2)-physicalShearMatrix M j n N a c weights ω := by
    funext ω
    exact assembly_physical_shear_sign M j n N a c weights ω
  rw [he]
  exact measurable_const.sub (physical_shear_matrix_measurable M j n N a c weights)

/-- The whole actual added-stream shear uses only shells strictly above j. -/
theorem assembly_physical_shear_later_measurable (M : ABKModel 2) (j n N : ℤ)
    (hjN : j ≤ N) (a c : ℝ) (weights : ℤ → ℝ) :
    @Measurable (Cutoff.CutoffSample 2) (FullBlockMat 2)
      (Model.cutoffLaterSigma (Set.Ioi j)) _ (assemblyPhysicalShearMatrix M j n N a c weights) := by
  have he : assemblyPhysicalShearMatrix M j n N a c weights =
      fun ω => (2:ℝ) • (1:FullBlockMat 2)-physicalShearMatrix M j n N a c weights ω := by
    funext ω
    exact assembly_physical_shear_sign M j n N a c weights ω
  rw [he]
  exact measurable_const.sub (physical_shear_matrix_later_measurable M j n N hjN a c weights)

/-- The actual added-stream shear has exactly the same squared-norm budget
as the conjugator; no weight or scalar premise changes. -/
theorem assembly_physical_shear_sq_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (j n N : ℤ) (hstrict : j < N)
    (hstate : nativeInductionState M h j) (a c : ℝ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (assemblyPhysicalShearMatrix M j n N a c weights ω)‖^2)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (2+80*(p+2)*(M.gamma*(N-j:ℝ)*(3:ℝ)^(2*M.gamma*(N-j:ℝ)))) := by
  have he : (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (assemblyPhysicalShearMatrix M j n N a c weights ω)‖^2) =
      fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
        (physicalShearMatrix M j n N a c weights ω)‖^2 := by
    funext ω
    rw [assemblyPhysicalShearMatrix,← assembly_constant_skew_neg_norm]
    rfl
  rw [he]
  exact physical_shear_matrix_sq_Lp M h hM j n N hstrict hstate a c weights hw p hp

end
end ASDExplicitGamma.Inverse
