module

public import ASDExplicitGamma.Native.OldSignedActualJointMeanProxy
public import ASDExplicitGamma.Native.OldSignedFlatJointL2
public import ASDExplicitGamma.Native.OldSignedSourceHistoryStationarity
public import ASDExplicitGamma.Native.OldSignedSourceBudgetNonnegative

/-! The spatial and probability direct sum retains the exact flat Hodge gain. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- Actual complete affine proxy, averaged over the common source partition. -/
def oldSignedActualJointSpatialProxy (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldSignedCellAverage (originCube 2 n) r (fun U =>
    oldSignedActualPlusMeanProxy M n r U.val U.property t b L ω+
      oldSignedActualMinusMeanProxy M n r U.val U.property t b L ω)

/-- Complete spatial/covariance/probability affine payment. Translation
stationarity makes the history budget common, and the exact Hodge identity
pays both disjoint load families by 2v, with no boundary overcharge. -/
theorem old_signed_joint_spatial_proxy_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (oldSignedActualJointSpatialProxy M n r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualJointSpatialProxy M n r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ((1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
        oldSignedSourceHistoryBudget M n (originCube 2 (n-(r:ℤ))) t j)*(2*b^2) := by
  let Q := originCube 2 n
  let U₀ := originCube 2 (n-(r:ℤ))
  let B := (1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
    oldSignedSourceHistoryBudget M n U₀ t j
  let p := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedActualPlusMeanProxy M n r U.val U.property t b L ω+
      oldSignedActualMinusMeanProxy M n r U.val U.property t b L ω
  have hp (U : OldSignedCellIndex Q r) :=
    old_signed_actual_joint_mean_proxy_payment M h hM hg n r hr U.val U.property t ht hstates b L
  have hi : Integrable (oldSignedActualJointSpatialProxy M n r t b L)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    unfold oldSignedActualJointSpatialProxy oldSignedCellAverage
    exact (integrable_finsetSum _ (fun U _ => (hp U).1)).const_mul _
  have he : (∫ ω,oldSignedActualJointSpatialProxy M n r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      oldSignedCellAverage Q r (fun U => ∫ ω,p U ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
    unfold oldSignedActualJointSpatialProxy oldSignedCellAverage
    rw [integral_const_mul,integral_finsetSum _ (fun U _ => (hp U).1)]
  have hbound (U : OldSignedCellIndex Q r) :
      (∫ ω,p U ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        B*(oldSignedFlatMeanSize Q U.val b L true^2+oldSignedFlatMeanSize Q U.val b L false^2) := by
    have hb := (hp U).2
    have hscale : U.val.scale=U₀.scale := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth U.property]
      rfl
    simp_rw [old_signed_source_history_budget_eq_scale M n U.val U₀ hscale t ht] at hb
    exact hb
  refine ⟨hi,?_⟩
  rw [he]
  have hh := old_signed_cell_average_mono Q r hbound
  rw [old_signed_cell_average_mul,old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => oldSignedFlatMeanSize Q U b L true^2+oldSignedFlatMeanSize Q U b L false^2)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (old_signed_joint_flat_mean_partition_bound Q r b L)
    (old_signed_source_directional_budget_nonneg M n U₀ t ht))

end
end ASDExplicitGamma.Native
