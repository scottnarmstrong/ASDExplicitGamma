module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalScales
public import ASDExplicitGamma.Scalar.OldHessianTrialFlatHistoryMoments
public import ASDExplicitGamma.Native.OldSignedQ1OscillationCaps

/-! Original fine-mesh oscillations meet the frozen scalar o coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The complete original minus oscillations pay precisely b squared o squared. -/
theorem old_hessian_physical_minus_oscillation (m : ℤ) (b : ℝ) :
    descendantsAverage (originCube 2 (m+129)) 134 (fun U =>
      oldSignedFlatOscillationSize (originCube 2 (m+129)) U b (q3ModelLength (m+1)) false^2)≤
        b^2*(evalReal scalarRealEnv lowerOscillationExpr)^2 := by
  let Q := originCube 2 (m+129)
  let L := q3ModelLength (m+1)
  let r := cubeScaleFactor Q/(3:ℝ)^134
  have hC := pow_le_pow_left₀ (Real.sqrt_nonneg _) old_signed_q1_planarC0_le 2
  have hnon : 0≤r^2*mainFlatSigmaSq b L := by unfold mainFlatSigmaSq; positivity
  have hh := mul_le_mul_of_nonneg_left hC hnon
  apply (old_signed_flat_minus_partition_oscillation_cap Q 134 b L).trans
  calc
    _ = (r^2*mainFlatSigmaSq b L)*planarC0^2 := by dsimp only [r]; ring
    _ ≤ (r^2*mainFlatSigmaSq b L)*(11/25:ℝ)^2 := hh
    _ = _ := by
      have hratio := old_hessian_physical_mesh_ratio m 5
      change r/L.val=1/(3:ℝ)^6 at hratio
      have he : r^2*mainFlatSigmaSq b L=b^2*(156/5:ℝ)*(r/L.val)^2 := by unfold mainFlatSigmaSq; ring
      rw [he,hratio]
      norm_num only [evalReal,lowerOscillationExpr,lowerS1Expr,sc,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤156/5)]
      ring

/-- The original bank remains inside the spatial matrix envelope, whose
annealed cap is exactly beta Mstar times the physical minus oscillation. -/
theorem old_hessian_physical_banked_matrix_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (fun ω => oldHessianGroupedBank M m ω*
      oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω*
      oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      ((14103/10000:ℝ)*evalReal scalarRealEnv lowerMExpr)*(b^2*(evalReal scalarRealEnv lowerOscillationExpr)^2) := by
  have hh := old_hessian_flat_banked_matrix_moment M h hM hg N hpast m hm b (q3ModelLength (m+1))
  refine ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_left (old_hessian_physical_minus_oscillation m b) ?_)⟩
  norm_num [evalReal,lowerMExpr,sc]
  positivity

end
end ASDExplicitGamma.Scalar
