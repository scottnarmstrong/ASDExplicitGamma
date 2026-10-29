module

public import ASDExplicitGamma.Gaussian.Q3WeightedProjection
public import ASDExplicitGamma.Gaussian.NormSquareMoment
public import ASDExplicitGamma.Gaussian.SeriesNormMomentLimit
public import Mathlib.Topology.Order.Basic

/-! # Sharp spatial norm moments of the physical product-q3 band -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Filter Set
open scoped ENNReal
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {n : ℕ} [NeZero n] (a b c d : ℝ) (β w : Fin n → ℝ)
  (L : Fin n → {l : ℝ // 0 < l})

/-- The exact mean plus sharp fluctuation bound for each retained physical noise projection. -/
theorem q3WeightedBandPartial_spatial_lpNorm_sq_le (hab : a < b) (hcd : c < d)
    (hw : ∀ i, |w i| ≤ 1) {p ell : ℝ} (hp : 2 ≤ p) (hell : 0 < ell)
    (hcost : Real.sqrt (∑ i, β i ^ 2 * min (L i).1
      (Real.sqrt (volume.real (closedRectangle a b c d)))) ≤ ell) (N : ℕ) :
    (eLpNorm (fun ω => ‖ContinuousMap.toLp 4 (spatialVolume (closedRectangle a b c d)) ℝ
      (q3WeightedBandPartialValue a b c d β w L N ω)‖) (ENNReal.ofReal p) standardGaussianInfinitePi).toReal ^ 2 ≤
      2 * Real.sqrt ((spatialVolume (closedRectangle a b c d)).real Set.univ *
        (3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2)) + 2 * p * ell ^ 2 := by
  let T := q3WeightedSpatialProjection (closedRectangle a b c d) β w L N
  let F : (Fin N → ℝ) → ℝ := fun x => ‖T (WithLp.toLp 2 x)‖
  have hF : AEStronglyMeasurable F (standardGaussianPi N) := by fun_prop
  have hT : ‖T‖ ≤ ell :=
    (q3WeightedSpatialProjection_norm_le (closedRectangle a b c d) β w L hw N).trans hcost
  have hfinite := gaussian_norm_lpNorm_sq_le T hell (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp) hT
  have hm := q3WeightedBandPartialValue_spatial_mean_sq_le a b c d β w L hab hcd N
  simp_rw [q3WeightedSpatialProjection_partial_eq a b c d β w L hab hcd N] at hm ⊢
  change (∫ ω : ℕ → ℝ, F (fun i : Fin N => ω i.val) ∂standardGaussianInfinitePi) ^ 2 ≤ _ at hm
  rw [integral_standardGaussian_firstCoordinates N F hF] at hm
  change (eLpNorm (fun ω : ℕ → ℝ => F (fun i : Fin N => ω i.val))
    (ENNReal.ofReal p) standardGaussianInfinitePi).toReal ^ 2 ≤ _
  rw [eLpNorm_standardGaussian_firstCoordinates N F hF]
  exact hfinite.2.trans (add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)

/-- The same bound for the full ordinary-H³ band image. The full Lᵖ convergence is supplied by
the source estimate, so no moment or convergence premise is inserted in the physical band statement. -/
theorem q3WeightedBandSeries_spatial_lpNorm_sq_le (hab : a < b) (hcd : c < d)
    (hw : ∀ i, |w i| ≤ 1) {p ell : ℝ} (hp : 2 ≤ p) (hell : 0 < ell)
    (hcost : Real.sqrt (∑ i, β i ^ 2 * min (L i).1
      (Real.sqrt (volume.real (closedRectangle a b c d)))) ≤ ell) :
    (eLpNorm (fun ω => q3WeightedBandH3Spatial a b c d β w L
      (q3BandSeries a b c d β L ω)) (ENNReal.ofReal p) standardGaussianInfinitePi).toReal ^ 2 ≤
      2 * Real.sqrt ((spatialVolume (closedRectangle a b c d)).real Set.univ *
        (3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2)) + 2 * p * ell ^ 2 := by
  have hpFact : Fact (2 ≤ p) := ⟨hp⟩
  apply @gaussianSeries_image_lpNorm_sq_le (Q3BandH3 a b c d β L)
    (SpatialLp4 (closedRectangle a b c d)) inferInstance
    (instQ3BandH3InnerProductSpace a b c d β L) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance (q3BandH3Directions a b c d β L)
    (q3BandH3Directions_summable a b c d β L) (q3WeightedBandH3Spatial a b c d β w L)
    p _ hpFact
  intro N
  have hm := memLp_q3WeightedBandPartialValue a b c d β w L hp N
  have hi := hm.continuousLinearMap_comp (ContinuousMap.toLp 4 (spatialVolume (closedRectangle a b c d)) ℝ)
  have he := eLpNorm_norm (p := ENNReal.ofReal p) (fun ω => ContinuousMap.toLp 4 (spatialVolume (closedRectangle a b c d)) ℝ
    (q3WeightedBandPartialValue a b c d β w L N ω)) hi.aestronglyMeasurable
  have hb := q3WeightedBandPartial_spatial_lpNorm_sq_le a b c d β w L hab hcd hw hp hell hcost N
  rw [he] at hb
  exact hb

/-- The vanishing-cost limit removes the temporary positive Lipschitz cap, including when every
shell amplitude is zero. -/
theorem q3WeightedBandSeries_spatial_lpNorm_sq_le_of_cost (hab : a < b) (hcd : c < d)
    (hw : ∀ i, |w i| ≤ 1) {p : ℝ} (hp : 2 ≤ p) :
    (eLpNorm (fun ω => q3WeightedBandH3Spatial a b c d β w L
      (q3BandSeries a b c d β L ω)) (ENNReal.ofReal p) standardGaussianInfinitePi).toReal ^ 2 ≤
      2 * Real.sqrt ((spatialVolume (closedRectangle a b c d)).real Set.univ *
        (3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2)) +
        2 * p * (∑ i, β i ^ 2 * min (L i).1
          (Real.sqrt (volume.real (closedRectangle a b c d)))) := by
  let cost : ℝ := ∑ i, β i ^ 2 * min (L i).1
    (Real.sqrt (volume.real (closedRectangle a b c d)))
  have hcost : 0 ≤ cost := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (sq_nonneg _)
      (le_min (L i).2.le (Real.sqrt_nonneg _))
  have hsqrt : 0 ≤ Real.sqrt cost := Real.sqrt_nonneg _
  have hlim : Tendsto
      (fun e : ℝ => 2 * Real.sqrt ((spatialVolume (closedRectangle a b c d)).real Set.univ *
        (3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2)) + 2 * p * (Real.sqrt cost + e) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (2 * Real.sqrt ((spatialVolume (closedRectangle a b c d)).real Set.univ *
        (3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2)) + 2 * p * cost)) := by
    have hc : Continuous (fun e : ℝ =>
        2 * Real.sqrt ((spatialVolume (closedRectangle a b c d)).real Set.univ *
          (3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2)) + 2 * p * (Real.sqrt cost + e) ^ 2) := by
      fun_prop
    have ht := hc.continuousAt.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    simpa [Real.sq_sqrt hcost] using ht
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with e he
  have hepos : 0 < e := by simpa using he
  have hell : 0 < Real.sqrt cost + e := add_pos_of_nonneg_of_pos hsqrt hepos
  have hcostle : Real.sqrt cost ≤ Real.sqrt cost + e := le_add_of_nonneg_right hepos.le
  have hb := q3WeightedBandSeries_spatial_lpNorm_sq_le a b c d β w L hab hcd hw hp hell
    (by simpa [cost] using hcostle)
  exact hb

end
end ASDExplicitGamma.Gaussian
