module

public import ASDExplicitGamma.Native.OldSignedJointSpatialProxy
public import ASDExplicitGamma.Native.OldSignedFlatProfileCaps

/-! Separate minus directional payment retains the half-trace normalization. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The spatial minus affine proxy, with the same actual parent coefficient. -/
def oldSignedActualMinusSpatialProxy (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldSignedCellAverage (originCube 2 n) r (fun U =>
    oldSignedActualMinusMeanProxy M n r U.val U.property t b L ω)

/-- Nonnegativity is retained before the probability contraction. -/
theorem old_signed_actual_minus_spatial_proxy_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0 ≤ oldSignedActualMinusSpatialProxy M n r t b L ω := by
  unfold oldSignedActualMinusSpatialProxy oldSignedCellAverage
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun U _ =>
    old_signed_actual_minus_mean_proxy_nonneg M n r U.val U.property t b L ω)

/-- The separate physical minus mean pays only one variance after the
spatial contraction. This is the half-trace gain in the linear derivative term. -/
theorem old_signed_minus_spatial_proxy_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (r : ℕ) (hr : r≤5)
    (t : ℝ) (ht : 0≤t ∧ t≤1)
    (hstates : ∀ l≤n,nativeInductionState M h l) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (oldSignedActualMinusSpatialProxy M n r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualMinusSpatialProxy M n r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      ((1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
        oldSignedSourceHistoryBudget M n (originCube 2 (n-(r:ℤ))) t j)*b^2 := by
  let Q := originCube 2 n
  let U₀ := originCube 2 (n-(r:ℤ))
  let B := (1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
    oldSignedSourceHistoryBudget M n U₀ t j
  let p := fun (U : OldSignedCellIndex Q r) ω =>
    oldSignedActualMinusMeanProxy M n r U.val U.property t b L ω
  have hp (U : OldSignedCellIndex Q r) :=
    old_signed_actual_minus_mean_proxy_payment M h hM hg n r hr U.val U.property t ht hstates b L
  have hi : Integrable (oldSignedActualMinusSpatialProxy M n r t b L)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    unfold oldSignedActualMinusSpatialProxy oldSignedCellAverage
    exact (integrable_finsetSum _ (fun U _ => (hp U).1)).const_mul _
  have he : (∫ ω,oldSignedActualMinusSpatialProxy M n r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      oldSignedCellAverage Q r (fun U => ∫ ω,p U ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
    unfold oldSignedActualMinusSpatialProxy oldSignedCellAverage
    rw [integral_const_mul,integral_finsetSum _ (fun U _ => (hp U).1)]
  have hB : 0≤B := old_signed_source_directional_budget_nonneg M n U₀ t ht
  have hbound (U : OldSignedCellIndex Q r) :
      (∫ ω,p U ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤B*oldSignedFlatL2Size Q U.val b L false^2 := by
    have hb := (hp U).2
    have hscale : U.val.scale=U₀.scale := by rw [scale_eq_sub_of_mem_descendantsAtDepth U.property]; rfl
    simp_rw [old_signed_source_history_budget_eq_scale M n U.val U₀ hscale t ht] at hb
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr
      (old_signed_flat_mean_size_le_l2 Q r b L false U.val U.property)
    exact hb.trans (mul_le_mul_of_nonneg_left hsq hB)
  refine ⟨hi,?_⟩
  rw [he]
  have hh := old_signed_cell_average_mono Q r hbound
  rw [old_signed_cell_average_mul,old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => oldSignedFlatL2Size Q U b L false^2)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (old_signed_flat_minus_partition_l2_cap Q r b L) hB)

end
end ASDExplicitGamma.Native
