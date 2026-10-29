module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalSourceMeans
public import ASDExplicitGamma.Scalar.UpperCellEnergyOldMatrixMean
public import ASDExplicitGamma.Numerics.Scalar.Lower

/-! True-frame mean floors and the unchanged fine affine penalty. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Homogenization.Book MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- The literal cutoff-law mean trace at the fine source scale has the
certified a5 cap, rather than a coarse-source replacement. -/
theorem old_hessian_fine_mean_trace_cap
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    (∫ a : RegCoeffField 2,traceDefect (cubeSet (originCube 2 (m-5))) a.toFun
      (Annealed.sigmaBar M m) ∂(Cutoff.coefficientCutoffLaw M m))≤evalReal scalarRealEnv lowerA5Expr := by
  have hc := old_hessian_physical_source_mean M h hM hg N hpast m hm 5 (Or.inr rfl)
  have he := old_hessian_physical_trace_mean_eq M (m+129) m 134
  have hs : m+129-(134:ℤ)=m-5 := by omega
  dsimp only at he
  norm_num only [Nat.cast_ofNat] at he
  rw [hs] at he
  have hsample : (∫ ω,cutoffTraceDefect M m (m-5) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      theta M*((nativeSourceExactMeanCaps.getD 5 0:ℚ):ℝ) := by
    rw [←he.2]
    exact hc.2
  have hnon : 0≤((nativeSourceExactMeanCaps.getD 5 0:ℚ):ℝ) := by norm_num [nativeSourceExactMeanCaps]
  have htheta := mul_le_mul_of_nonneg_right (cold_theta_le_one M hg) hnon
  rw [one_mul] at htheta
  have hi := integrable_traceDefect_cutoffLaw M m (originCube 2 (m-5)) (Annealed.sigmaBar M m)
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi ⊢
  rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable hi.aestronglyMeasurable]
  exact (hsample.trans htheta).trans_eq (by norm_num [nativeSourceExactMeanCaps,evalReal,lowerA5Expr,sc])

/-- Both actual mean block excesses are nonnegative and their sum has one
half-trace charge, uniformly at every translated fine source cell. -/
theorem old_hessian_fine_mean_matrix
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    ∃ A B : ℝ,0≤A ∧ 0≤B ∧ A+B≤evalReal scalarRealEnv lowerA5Expr/2 ∧
      ∀ U : TriadicCube 2,U.scale=m-5 →
        frameMatrix (Annealed.sigmaBar M m) (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet U))=
          Ch02.blockDiag ((1+A) • (1:Mat 2)) ((1+B) • (1:Mat 2)) := by
  obtain ⟨a,b,ha,hb,heq⟩ := exists_trueFrame_mean_scalars M m (m-5)
  have htrace := old_hessian_fine_mean_trace_cap M h hM hg N hpast m hm
  rw [integral_traceDefect_eq_annealed_trace] at htrace
  have hzero := heq 0
  rw [translateSet_zero] at hzero
  have hUL := congrArg (fun C : BlockMat 2 => Matrix.trace C.upperLeft) hzero
  have hLR := congrArg (fun C : BlockMat 2 => Matrix.trace C.lowerRight) hzero
  simp only [frameMatrix,Ch02.blockDiag,Matrix.trace_smul,smul_eq_mul,Matrix.trace_one,Fintype.card_fin] at hUL hLR
  rw [hUL,hLR] at htrace
  norm_num only [Nat.cast_ofNat] at htrace
  refine ⟨a-1,b-1,sub_nonneg.mpr ha,sub_nonneg.mpr hb,?_,?_⟩
  · linarith only [htrace]
  · intro U hU
    rw [cubeSet_eq_translateSet_originCube_of_triadicCube U,hU,heq]
    congr 1 <;> congr 1 <;> ring

end
end ASDExplicitGamma.Scalar
