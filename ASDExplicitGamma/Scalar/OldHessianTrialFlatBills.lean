module

public import ASDExplicitGamma.Scalar.OldHessianTrialFlatTangent
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalFlatCovariance
public import ASDExplicitGamma.Scalar.OldHessianTrialFlatBoundaryAllObservers
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalOscillation

/-! Numerical q128 substitution of the Bflat boundary energy into the original
flat covariance coefficient (bill 8), and the frozen value of the flat tail. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

theorem old_hessian_flat_tail_value :
    evalReal scalarRealEnv lowerFlatTailExpr = (429/175:ℝ)*(1/(3:ℝ)^128) := by
  norm_num [evalReal,lowerFlatTailExpr,sc]

/-- The actual Bflat energy at the original observer is below `b² q`, with the
frozen flat tail as `q`. -/
theorem old_hessian_physical_flat_boundary (m : ℤ) (b : ℝ) (hb : 0<b) :
    oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b (q3ModelLength (m+1))≤
      b^2*evalReal scalarRealEnv lowerFlatTailExpr := by
  rw [old_hessian_flat_tail_value]
  exact ASDExplicitGamma.Main.old_hessian_flat_boundary_q128 m b hb

/-- The covariance coefficient is at most `b² z` for the frozen `z`. -/
theorem old_hessian_physical_flat_covariance_z (m : ℤ) (b : ℝ) (hb : 0<b) :
    oldHessianFlatCovarianceCap (originCube 2 (m+129)) 134 b (q3ModelLength (m+1))≤
      b^2*evalReal scalarRealEnv lowerZExpr := by
  have hq : 0≤evalReal scalarRealEnv lowerFlatTailExpr := by norm_num [evalReal,lowerFlatTailExpr,sc]
  have h := old_hessian_physical_flat_covariance_of_boundary m b _ hq
    (old_hessian_physical_flat_boundary m b hb)
  refine h.trans_eq ?_
  norm_num only [lowerZExpr,evalReal,sc]
  ring

/-- Eighth bill: the exact signed inverse bulk is retained and the harmonic
covariance remainder is paid by `b² * lowerTerm8Expr`. -/
theorem old_hessian_actual_eighth_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) (hb : 0<b) :
    Integrable (oldHessianFlatTangentEnvelope M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 (m+129)
      let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω)
      Summable (fun n => oldHessianFlatTangentTerm M m b n ω) ∧
      (∑' n,oldHessianFlatTangentTerm M m b n ω)≤
        -(431/500:ℝ)*b^2*(Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
          oldHessianFlatTangentEnvelope M m b ω) ∧
    (∫ ω,oldHessianFlatTangentEnvelope M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      b^2*evalReal scalarRealEnv lowerTerm8Expr := by
  obtain ⟨h1,h2,h3⟩ := old_hessian_actual_flat_tangent M h hM hg N hpast m hm b
  refine ⟨h1,h2,h3.trans ?_⟩
  have hz := old_hessian_physical_flat_covariance_z m b hb
  have hs : 0≤Real.sqrt (evalReal scalarRealEnv lowerXiExpr) := Real.sqrt_nonneg _
  calc (2*(431/500:ℝ)*oldHessianFlatCovarianceCap (originCube 2 (m+129)) 134 b (q3ModelLength (m+1)))*
        Real.sqrt (evalReal scalarRealEnv lowerXiExpr)
      ≤ (2*(431/500:ℝ)*(b^2*evalReal scalarRealEnv lowerZExpr))*Real.sqrt (evalReal scalarRealEnv lowerXiExpr) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by norm_num)) hs
    _ = _ := by
      simp only [lowerTerm8Expr,lowerTExpr,evalReal,sc]
      ring

end
end ASDExplicitGamma.Scalar
