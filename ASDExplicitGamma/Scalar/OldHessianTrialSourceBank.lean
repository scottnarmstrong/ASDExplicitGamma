module

public import ASDExplicitGamma.Scalar.OldHessianTrialCoarseThetaJoin
public import ASDExplicitGamma.Scalar.OldHessianTrialSourceTraceNorm
public import ASDExplicitGamma.Scalar.OldHessianTrialCoarseColumnBudget

/-! Actual mixed-source and projected-residual bounds on one common bank
 event. The coarse potentials keep their shifted root-zero weak payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Both spatial source components are bounded by the actual grouped bank,
coarse source trace, and convergent OLD weak proxy on the original sample. -/
theorem old_hessian_actual_source_components_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 (m+129)
      let k := oldHessianOldOpenCoefficient (m+129) m ω
      (∑ i : Fin 2,lemmaVTiledWeakEnergy Q 134
        (oldHessianMixedPotential Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1 k i).toH1Function.grad) ≤
        oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 4 ω ∧
      ∀ (b : ℝ) (L : {l : ℝ // 0<l}),
        (∑ i : Fin 2,oldHessianCoarseColumnBill Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1 k (basisVec i) b L) ≤
        oldHessianCoarseColumnCoefficient Q 133 b L^2*
          (inverseHistoryDiscount^2*oldHessianGroupedOldTheta M m ω) := by
  filter_upwards [old_hessian_actual_fine_histories_le_bank M h hM hg N hpast m hm,
    old_hessian_actual_coarse_theta_join M h hM hg N hpast m hm] with ω hbank htheta
  dsimp only
  constructor
  · exact (old_hessian_mixed_joint_coarse_trace (originCube 2 (m+129)) 133 134
      M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
      (oldHessianOldOpenCoefficient (m+129) m ω)).trans
      (mul_le_mul_of_nonneg_right (hbank 5 (by norm_num))
        (old_hessian_source_trace_nonneg M m 4 ω))
  · intro b L
    rw [old_hessian_coarse_column_joint_factor]
    exact mul_le_mul_of_nonneg_left htheta.2 (sq_nonneg _)

end
end ASDExplicitGamma.Scalar
