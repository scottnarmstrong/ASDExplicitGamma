module

public import ASDExplicitGamma.Gaussian.Q3WeightedPartialMoments
public import ASDExplicitGamma.Gaussian.FiniteProjectionLaw

/-! # The exact finite-dimensional physical projections and their Cameron–Martin bound -/

@[expose] public section

open MeasureTheory Homogenization
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- The retained physical white-noise projection of an attenuated finite band. -/
noncomputable def q3WeightedSpatialProjection {b : ℕ} [NeZero b]
    (K : Set (Vec 2)) [CompactSpace K] (β w : Fin b → ℝ)
    (L : Fin b → {l : ℝ // 0 < l}) (N : ℕ) : EuclideanSpace ℝ (Fin N) →L[ℝ] SpatialLp4 K :=
  (q3WeightedBandSpatialOperator K β w L).comp
    (orthogonalInputMap (fun i : Fin N => q3BandWhiteDirections (b := b) i.val))

/-- The full physical bound holds independently of the retained noise dimension. -/
theorem q3WeightedSpatialProjection_norm_le {b : ℕ} [NeZero b]
    (K : Set (Vec 2)) [CompactSpace K] (β w : Fin b → ℝ)
    (L : Fin b → {l : ℝ // 0 < l}) (hw : ∀ i, |w i| ≤ 1) (N : ℕ) :
    ‖q3WeightedSpatialProjection K β w L N‖ ≤
      Real.sqrt (∑ i, β i ^ 2 * min (L i).1 (Real.sqrt (volume.real K))) := by
  have hv : Pairwise (fun i j : Fin N =>
      ⟪q3BandWhiteDirections (b := b) i.val, q3BandWhiteDirections j.val⟫ = 0) := by
    intro i j hij
    exact q3BandWhiteDirections_orthogonal (fun he => hij (Fin.ext he))
  have hh := orthogonalInputMap_norm_le_one
    (fun i : Fin N => q3BandWhiteDirections (b := b) i.val) hv
    (fun i => q3BandWhiteDirections_norm_le_one i.val)
  calc
    _ ≤ ‖q3WeightedBandSpatialOperator K β w L‖ *
        ‖orthogonalInputMap (fun i : Fin N => q3BandWhiteDirections (b := b) i.val)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖q3WeightedBandSpatialOperator K β w L‖ * 1 :=
      mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact q3WeightedBandSpatialOperator_norm_le K β w L hw

/-- The physical projection is the spatial image of the retained H³ series, pointwise. -/
theorem q3WeightedSpatialProjection_partial_eq {n : ℕ} [NeZero n] (a b c d : ℝ)
    (β w : Fin n → ℝ) (L : Fin n → {l : ℝ // 0 < l}) (hab : a < b) (hcd : c < d)
    (N : ℕ) (ω : ℕ → ℝ) :
    ContinuousMap.toLp 4 (spatialVolume (closedRectangle a b c d)) ℝ
      (q3WeightedBandPartialValue a b c d β w L N ω) =
      q3WeightedSpatialProjection (closedRectangle a b c d) β w L N
        (WithLp.toLp 2 (fun i : Fin N => ω i.val)) := by
  change q3WeightedBandH3Spatial a b c d β w L
    (gaussianPartialSum (q3BandH3Directions a b c d β L) N ω) = _
  rw [gaussianPartialSum, map_sum]
  simp_rw [map_smul, q3WeightedBandH3Spatial_direction a b c d β w L hab hcd]
  rw [q3WeightedSpatialProjection, ContinuousLinearMap.comp_apply, orthogonalInputMap_apply, map_sum]
  simp_rw [map_smul]
  exact (Fin.sum_univ_eq_sum_range (fun j => ω j • q3WeightedBandSpatialOperator
    (closedRectangle a b c d) β w L (q3BandWhiteDirections j)) N).symm

end ASDExplicitGamma.Gaussian
