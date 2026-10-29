module

public import ASDExplicitGamma.Native.OldSignedActualTiledProfiles
public import ASDExplicitGamma.Native.OldSignedJointSpatialProxy
public import ASDExplicitGamma.Native.OldSignedSqrtProductExpectation

/-! The dominant affine mixed cross after spatial and probability contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Gaussian Algsuperdiff.Section3
noncomputable section

/-- The actual joint spatial affine proxy is nonnegative. -/
theorem old_signed_actual_joint_spatial_proxy_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0 ≤ oldSignedActualJointSpatialProxy M n r t b L ω := by
  unfold oldSignedActualJointSpatialProxy oldSignedCellAverage
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro U _
  exact add_nonneg (old_signed_actual_plus_mean_proxy_nonneg M n r U.val U.property t b L ω)
    (old_signed_actual_minus_mean_proxy_nonneg M n r U.val U.property t b L ω)

/-- Joint affine/projection contraction in the actual correlated law. Both
factors are assembled over the entire tiling before Cauchy--Schwarz; the
complete weak budget and exact flat Hodge energy supply the two moments. -/
theorem old_signed_joint_annealed_contraction
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let B := (1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
      oldSignedSourceHistoryBudget M n (originCube 2 (n-(r:ℤ))) t j
    Integrable (fun ω => Real.sqrt (oldSignedActualTiledWeakProxy M n r t ω)*
      Real.sqrt (oldSignedActualJointSpatialProxy M n r t b L ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (oldSignedActualTiledWeakProxy M n r t ω)*
      Real.sqrt (oldSignedActualJointSpatialProxy M n r t b L ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (2*B)*|b| := by
  intro B
  have hv := old_signed_tiled_history_payment M h hM hg n r hr t ht hstates
  have hp := old_signed_joint_spatial_proxy_payment M h hM hg n r hr t ht hstates b L
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure
    _ _ hv.1 hp.1 (old_signed_actual_tiled_weak_proxy_nonneg M n r t ht)
    (old_signed_actual_joint_spatial_proxy_nonneg M n r t b L)
  have hB : 0 ≤ B := old_signed_source_directional_budget_nonneg M n
    (originCube 2 (n-(r:ℤ))) t ht
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hle := mul_le_mul (Real.sqrt_le_sqrt hv.2) (Real.sqrt_le_sqrt hp.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg (2*B))
  apply hle.trans_eq
  change Real.sqrt (2*B)*Real.sqrt (B*(2*b^2))=(2*B)*|b|
  rw [show B*(2*b^2)=(2*B)*b^2 by ring,
    Real.sqrt_mul (mul_nonneg (by norm_num) hB),Real.sqrt_sq_eq_abs]
  rw [←mul_assoc,Real.mul_self_sqrt (mul_nonneg (by norm_num) hB)]

end
end ASDExplicitGamma.Native
