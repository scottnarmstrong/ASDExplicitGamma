module

public import ASDExplicitGamma.Scalar.OldHessianTrialFineMeanMatrix
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusMeanBank
public import ASDExplicitGamma.Native.OldSignedDirectionalIntegral

/-! Actual fine upper-block mean, before any cell-dependent deterministic load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Homogenization.Book MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Every fixed actual source-cell top quadratic form has its original
fine a5 half-trace cap; all entry integrability is supplied internally. -/
theorem old_hessian_fine_top_quadratic_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : OldSignedCellIndex (originCube 2 (m+129)) 134) (e : Vec 2) :
    let A := fun ω => (coarseBlockMatrix (openCubeSet U.val)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω))).upperLeft
    Integrable (fun ω => vecDot e (matVecMul (A ω) e)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,vecDot e (matVecMul (A ω) e) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
        (1+evalReal scalarRealEnv lowerA5Expr/2)*vecNormSq e := by
  intro A
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have he (ω) : A ω=(frameMatrix (Annealed.sigmaBar M m)
      (coarseBlockMatrix (cubeSet U.val) (Cutoff.coefficientCutoff M.nu m ω).toFun)).upperLeft :=
    congrArg BlockMat.upperLeft (old_hessian_old_open_coarse_frame M (m+129) m ω U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property))
  have hi (i j : Fin 2) : Integrable (fun ω => A ω i j) μ := by
    simp_rw [he]
    exact upper_cell_old_framed_entry_integrable M m U.val (Annealed.sigmaBar M m) (.inl i) (.inl j)
  have hscale : U.val.scale=m-5 := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth U.property
    change U.val.scale=m+129-134 at hs
    omega
  obtain ⟨c,d,hc,hd,hcd,hmat⟩ := old_hessian_fine_mean_matrix M h hM hg N hpast m hm
  have hmean (i j : Fin 2) : (∫ ω,A ω i j ∂μ)=if i=j then 1+c else 0 := by
    simp_rw [he]
    have hh := upper_cell_old_framed_entry_integral M m U.val (Annealed.sigmaBar M m) (.inl i) (.inl j)
    rw [hmat U.val hscale] at hh
    simpa only [blockMatEntry,Ch02.blockDiag,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero] using hh
  refine ⟨old_signed_quadratic_integrable μ A hi e,?_⟩
  rw [old_signed_integral_scalar_quadratic μ A hi (1+c) hmean e]
  apply mul_le_mul_of_nonneg_right _ (vecNormSq_nonneg e)
  linarith only [hcd,hd]

/-- The actual top quadratic is nonnegative before any mode sum or
expectation; this is the physical local canonical energy. -/
theorem old_hessian_top_quadratic_nonneg (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    0≤vecDot e (matVecMul (coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField nu sigma k)).upperLeft e) := by
  have hh := old_signed_affine_energy Q nu sigma hnu hsigma k (e,0)
  have hn : 0≤oldSignedEnergyPairing Q nu sigma k
      (scalarResidualField Q nu sigma hnu hsigma k ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField (e,0)))
      (scalarResidualField Q nu sigma hnu hsigma k ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField (e,0))) := by
    rw [←old_signed_energy_inner_fields Q nu sigma hnu hsigma k (Lp.memLp _) (Lp.memLp _)]
    exact real_inner_self_nonneg
  rw [hh] at hn
  simpa only [blockVecDot,blockMatVecMul,matVecMul_zero,add_zero,vecDot_zero_left] using hn

end
end ASDExplicitGamma.Scalar
