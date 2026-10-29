module

public import ASDExplicitGamma.Gaussian.SpatialLpFourth
public import ASDExplicitGamma.Gaussian.BandOperatorNorm
public import ASDExplicitGamma.Gaussian.OrthogonalBandInputs
public import ASDExplicitGamma.Gaussian.Q3ModelH3Realization

/-! # The physical finite band's spatial covariance operator -/

@[expose] public section

open MeasureTheory Homogenization
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- The input space retains independent white-noise coordinates for every shell. -/
abbrev Q3BandWhiteNoise (b : ℕ) := PiLp 2 (fun _ : Fin b => WhiteNoise)

/-- Coarse and fine bounds combine before summing the shell coordinates. -/
theorem q3SpatialLp4Operator_norm_le_min (K : Set (Vec 2)) [CompactSpace K]
    (β : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise) :
    ‖q3SpatialLp4Operator K β L u‖ ≤
      Real.sqrt (β ^ 2 * min L.1 (Real.sqrt (volume.real K))) * ‖u‖ := by
  have hnonneg : 0 ≤ β ^ 2 * min L.1 (Real.sqrt (volume.real K)) :=
    mul_nonneg (sq_nonneg β) (le_min L.2.le (Real.sqrt_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hnonneg]
  by_cases hL : L.1 ≤ Real.sqrt (volume.real K)
  · rw [min_eq_left hL]
    exact q3SpatialLp4Operator_norm_sq_le_fine K β L u
  · rw [min_eq_right (le_of_not_ge hL)]
    exact q3SpatialLp4Operator_norm_sq_le_coarse K β L u

/-- The noise input sequence covers the actual white basis with zero padding in each shell. -/
noncomputable def q3BandWhiteDirections {b : ℕ} [NeZero b] : ℕ → Q3BandWhiteNoise b :=
  finiteDirections (fun _ : Fin b => WhiteNoise) (fun _ => gaussEnumerated whiteBasis)

theorem q3BandWhiteDirections_orthogonal {b : ℕ} [NeZero b] :
    Pairwise (fun i j => ⟪q3BandWhiteDirections (b := b) i, q3BandWhiteDirections j⟫ = 0) :=
  finiteDirections_orthogonal _ (fun _ => enumerated_orthogonal _ whiteBasis.orthonormal)

theorem q3BandWhiteDirections_norm_le_one {b : ℕ} [NeZero b] (n : ℕ) :
    ‖q3BandWhiteDirections (b := b) n‖ ≤ 1 :=
  finiteDirections_norm_le_one _ (fun _ => enumerated_norm_le_one _ whiteBasis.orthonormal) n

end ASDExplicitGamma.Gaussian
