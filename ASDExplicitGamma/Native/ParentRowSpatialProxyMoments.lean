module

public import ASDExplicitGamma.Native.ParentRowWeakAllowance
public import ASDExplicitGamma.Native.ParentRowFlatRootPanel
public import ASDExplicitGamma.Native.ParentRowDerivativeProfiles
public import ASDExplicitGamma.Native.OldSignedCellAverageExpectation

/-! Sharp joint and minus spatial proxy expectations on the actual parent band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- The two complete affine families cost the common half-trace budget
multiplied by 2b² after the spatial contraction. -/
theorem parent_row_joint_spatial_proxy_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) (r : ℕ) (hr : r=5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (parentBoundaryBandJointSpatialProxy M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ omega,parentBoundaryBandJointSpatialProxy M n height r t b L omega
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (theta M*parentRowWeakAllowance height t)*b^2 := by
  let Q := originCube 2 n
  let B := (theta M/2)*parentRowWeakAllowance height t
  let p := fun U omega => oldSignedFlatDirectionalMeanProxy Q U
    (parentBoundaryBandFrameField M n height t omega) b L true+
    oldSignedFlatDirectionalMeanProxy Q U (parentBoundaryBandFrameField M n height t omega) b L false
  have hp (U) (hU : U∈descendantsAtDepth Q r) (plus : Bool) :=
    parent_row_flat_proxy_payment M h hM hg n height hheight hh16 r hr U hU t ht hpast hstate b L plus
  have hi (U) (hU : U∈descendantsAtDepth Q r) : Integrable (p U) (Cutoff.cutoffSampleLaw M).toMeasure :=
    (hp U hU true).1.add (hp U hU false).1
  have hb (U) (hU : U∈descendantsAtDepth Q r) :
      (∫ omega,p U omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
        B*(oldSignedFlatMeanSize Q U b L true^2+oldSignedFlatMeanSize Q U b L false^2) := by
    have hplus := (hp U hU true).2
    have hminus := (hp U hU false).2
    dsimp only [p]
    rw [integral_add (hp U hU true).1 (hp U hU false).1,mul_add]
    exact add_le_add hplus hminus
  have hint : Integrable (parentBoundaryBandJointSpatialProxy M n height r t b L)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    unfold parentBoundaryBandJointSpatialProxy descendantsAverage
    exact (integrable_finsetSum _ hi).const_mul _
  refine ⟨hint,?_⟩
  change (∫ omega,descendantsAverage Q r (fun U => p U omega) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤_
  rw [old_signed_integral_descendants_average _ Q r p hi]
  have hh := old_signed_cell_average_mono Q r (fun U => hb U.val U.property)
  rw [old_signed_cell_average_mul,old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => oldSignedFlatMeanSize Q U b L true^2+oldSignedFlatMeanSize Q U b L false^2)] at hh
  rw [old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => ∫ omega,p U omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)] at hh
  have hB : 0≤B := mul_nonneg (div_nonneg (cold_theta_pos M).le (by norm_num))
    (parent_row_weak_allowance_nonneg height t ht.1)
  exact (hh.trans (mul_le_mul_of_nonneg_left (old_signed_joint_flat_mean_partition_bound Q r b L) hB)).trans_eq (by dsimp only [B]; ring)


/-- The actual minus proxy keeps the sharp directional half and its exact
parent Dirichlet energy after the complete spatial average. -/
theorem parent_row_minus_spatial_proxy_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (parentRowMinusSpatialProxy M n height r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowMinusSpatialProxy M n height r t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      ((theta M/2)*parentRowWeakAllowance height t)*parentBoundaryDirichletEnergy (originCube 2 n) b L := by
  let Q := originCube 2 n
  let B := (theta M/2)*parentRowWeakAllowance height t
  let p := fun (U : OldSignedCellIndex Q r) ω => oldSignedFlatDirectionalMeanProxy Q U.val
    (parentBoundaryBandFrameField M n height t ω) b L false
  have hp (U : OldSignedCellIndex Q r) :=
    parent_row_flat_proxy_payment M h hM hg n height hheight hh16 r hr U.val U.property t ht hpast hstate b L false
  refine ⟨old_signed_cell_average_integrable _ Q r p (fun U => (hp U).1), ?_⟩
  change (∫ ω,oldSignedCellAverage Q r (fun U => p U ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤_
  rw [old_signed_cell_average_integral _ Q r p (fun U => (hp U).1)]
  have hh := old_signed_cell_average_mono Q r (fun U => (hp U).2)
  rw [old_signed_cell_average_mul,old_signed_cell_average_eq_descendantsAverage Q r
    (fun U => oldSignedFlatMeanSize Q U b L false^2)] at hh
  have hB : 0≤B := mul_nonneg (div_nonneg (cold_theta_pos M).le (by norm_num))
    (parent_row_weak_allowance_nonneg height t ht.1)
  exact hh.trans (mul_le_mul_of_nonneg_left (parent_row_minus_mean_partition Q r b L) hB)

end
end ASDExplicitGamma.Native
