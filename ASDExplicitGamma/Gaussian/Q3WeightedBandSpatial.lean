module

public import ASDExplicitGamma.Gaussian.Q3BandSpatialOperator
public import ASDExplicitGamma.Gaussian.Q3BandH3

/-! # Identifying attenuated physical spatial operators with the ordinary-H³ directions -/

@[expose] public section

open MeasureTheory Homogenization

namespace ASDExplicitGamma.Gaussian

/-- Deterministic attenuations on the independent white-noise input coordinates. -/
noncomputable def q3WeightedBandSpatialOperator {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (β w : Fin b → ℝ) (L : Fin b → {l : ℝ // 0 < l}) :
    Q3BandWhiteNoise b →L[ℝ] SpatialLp4 K :=
  finiteFactor (fun _ : Fin b => WhiteNoise)
    (fun i => w i • q3SpatialLp4Operator K (β i) (L i))

/-- Attenuations of magnitude at most one preserve the sharp physical band bound. -/
theorem q3WeightedBandSpatialOperator_norm_le {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (β w : Fin b → ℝ) (L : Fin b → {l : ℝ // 0 < l}) (hw : ∀ i, |w i| ≤ 1) :
    ‖q3WeightedBandSpatialOperator K β w L‖ ≤
      Real.sqrt (∑ i, β i ^ 2 * min (L i).1 (Real.sqrt (volume.real K))) := by
  have hh := finiteFactor_norm_le_sqrt (fun _ : Fin b => WhiteNoise)
    (fun i => w i • q3SpatialLp4Operator K (β i) (L i))
    (fun i => Real.sqrt (β i ^ 2 * min (L i).1 (Real.sqrt (volume.real K)))) (fun i u => by
      change ‖w i • q3SpatialLp4Operator K (β i) (L i) u‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ 1 * ‖q3SpatialLp4Operator K (β i) (L i) u‖ :=
          mul_le_mul_of_nonneg_right (hw i) (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact q3SpatialLp4Operator_norm_le_min K (β i) (L i) u)
  have he (i : Fin b) : Real.sqrt (β i ^ 2 * min (L i).1 (Real.sqrt (volume.real K))) ^ 2 =
      β i ^ 2 * min (L i).1 (Real.sqrt (volume.real K)) :=
    Real.sq_sqrt (mul_nonneg (sq_nonneg _) (le_min (L i).2.le (Real.sqrt_nonneg _)))
  simp_rw [he] at hh
  exact hh

/-- The value image of a single enumerated H³ direction is its literal white-noise convolution. -/
theorem q3H3Directions_value_eq_convolution (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (n : ℕ) :
    q3H3RangeValue a b c d β L (q3H3Directions a b c d β L whiteBasis n) =
      q3ContinuousOperator (closedRectangle a b c d) β L h3Zero (gaussEnumerated whiteBasis n) := by
  classical
  let := Encodable.ofCountable whiteBasisIndex
  by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
  · obtain ⟨j, rfl⟩ := hn
    rw [q3H3Directions, enumerated_encode, enumerated_encode]
    apply ContinuousMap.ext
    intro x
    exact q3H3RangeValue_factor a b c d β hab hcd L (whiteBasis j) x
  · rw [q3H3Directions, gaussEnumerated, gaussEnumerated,
      Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
    simp only [Pi.zero_apply, map_zero]

section
variable {n : ℕ} [NeZero n] (a b c d : ℝ) (β w : Fin n → ℝ)
  (L : Fin n → {l : ℝ // 0 < l})

/-- The actual weighted values on the complete ordinary-H³ joint shell carrier. -/
noncomputable def q3WeightedBandH3Value :
    Q3BandH3 a b c d β L →L[ℝ] C(closedRectangle a b c d, ℝ) :=
  @finiteFactor n (fun i => Q3H3Range a b c d (β i) (L i))
    (fun _ => inferInstance) (fun _ => inferInstance) _ inferInstance inferInstance
    (fun i => w i • q3H3RangeValue a b c d (β i) (L i))

/-- The weighted spatial norm is a bounded image of the same H³ series. -/
noncomputable def q3WeightedBandH3Spatial :
    Q3BandH3 a b c d β L →L[ℝ] SpatialLp4 (closedRectangle a b c d) :=
  (ContinuousMap.toLp 4 (spatialVolume (closedRectangle a b c d)) ℝ).comp
    (q3WeightedBandH3Value a b c d β w L)

/-- Every retained H³ direction agrees exactly with the physical white-noise spatial factor.
This is a pointwise direction identity, prior to taking any Gaussian law or limit. -/
theorem q3WeightedBandH3Spatial_direction (hab : a < b) (hcd : c < d) (j : ℕ) :
    q3WeightedBandH3Spatial a b c d β w L (q3BandH3Directions a b c d β L j) =
      q3WeightedBandSpatialOperator (closedRectangle a b c d) β w L (q3BandWhiteDirections j) := by
  dsimp only [q3WeightedBandH3Spatial, q3WeightedBandH3Value, q3BandH3Directions,
    q3WeightedBandSpatialOperator, q3BandWhiteDirections, ContinuousLinearMap.comp_apply]
  rw [finiteDirections, finiteDirections, finiteFactor_single, finiteFactor_single]
  simp only [smul_apply, map_smul]
  rw [q3H3Directions_value_eq_convolution a b c d _ hab hcd]
  rfl

end
end ASDExplicitGamma.Gaussian
