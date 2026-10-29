module

public import ASDExplicitGamma.Scalar.OldHessianTrialParentDepthBank
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaMoments
public import ASDExplicitGamma.Native.OldSignedTiledParentWeak

/-! The original parent weak profile uses the same actual grouped OLD proxy. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Literal parent weak trace on the original fine source tiling. -/
def oldHessianParentWeakTrace (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 (m+129)
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) (oldHessianOldOpenCoefficient (m+129) m ω)
  rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (134+j))
    (fun j => descendantsAverage Q (134+j) (fun U => traceDefect (openCubeSet U) a 1))

/-- Every parent weak depth is paid before summation by its actual r5
bank and the identical full fine trace. Convergence follows from ellipticity. -/
theorem old_hessian_actual_parent_weak_trace_le_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      oldHessianParentWeakTrace M m ω≤oldHessianGroupedOldTheta M m ω := by
  filter_upwards [old_hessian_actual_parent_depth_bank M h hM hg N hpast m hm,
    old_hessian_grouped_old_theta_summable M h hM hg N hpast m hm] with ω hbank hgroup
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k
  let p := 1-inverseHistoryDiscount^2
  let T := fun j => descendantsAverage Q (134+j) (fun U => traceDefect (openCubeSet U) a 1)
  let E := fun j => inverseHistoryDiscount^(2*j)*lemmaVInverseDepthMax Q a (134+j)*T j
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k
  have htrace (j) : T j=oldHessianFineDepthTrace M m j ω := old_hessian_old_open_trace_sequence M (m+129) m ω (134+j)
  have hp : 0≤p := sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hs := old_signed_shifted_weak_trace_proxy_summable Q 134 a hEll
  have hterm (j : ℕ) : p*E j≤oldHessianGroupedOldThetaTerm M m j ω := by
    have ht : 0≤T j := by rw [htrace]; exact old_hessian_fine_depth_trace_nonneg M m j ω
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hbank j) ht)
      (mul_nonneg hp (pow_nonneg inverse_history_discount_range.1.le (2*j)))
    convert hh using 1 <;>
      (dsimp only [oldHessianGroupedOldThetaTerm,p,E]; rw [htrace]; norm_num only [inverseBankCap]; ring)
  have hh := (hs.mul_left p).tsum_le_tsum hterm hgroup
  rw [tsum_mul_left,←old_hessian_grouped_old_theta_series] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
