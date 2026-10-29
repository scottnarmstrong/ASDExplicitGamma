module

public import ASDExplicitGamma.Native.OldSignedFlatPositiveSeries
public import ASDExplicitGamma.Native.OldSignedAffineCorrector

/-! Genuine complete cell-mean square series of the actual OLD flat
sources, used in the signed affine contribution of AN (5.2). -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The positive source norm retains every actual cell-mean coordinate. -/
theorem old_signed_vector_mean_sq_le_positive (Q : TriadicCube 2) (f : Vec 2 → Vec 2) :
    (∑ k : Fin 2,cubeAverage Q (fun x => f x k)^2)≤vectorPositiveHaarNorm Q f^2 := by
  rw [vectorPositiveHaarNorm,Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg Q f)]
  unfold vectorPositiveHaarEnergy
  apply Finset.sum_le_sum
  intro k _
  unfold primalEnergy
  rw [cubeIncrement_zero,energy_projection_zero]
  exact le_add_of_nonneg_right (tsum_nonneg (fun j =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (energy_nonneg Q _)))

/-- A pure-second source's block-mean size is bounded by its actual
positive vector norm, with the first zero block kept exact. -/
theorem old_signed_pure_second_mean_norm_le_positive (Q : TriadicCube 2) (f : Vec 2 → Vec 2) :
    blockVecDot (oldSignedBlockMean Q (fun x => (0,f x)))
      (oldSignedBlockMean Q (fun x => (0,f x)))≤vectorPositiveHaarNorm Q f^2 := by
  have he : blockVecDot (oldSignedBlockMean Q (fun x => (0,f x)))
      (oldSignedBlockMean Q (fun x => (0,f x)))=∑ k : Fin 2,cubeAverage Q (fun x => f x k)^2 := by
    simp only [oldSignedBlockMean,blockVecDot,vecDot,Pi.zero_apply,cubeAverage_const,zero_mul,
      Finset.sum_const_zero,zero_add,pow_two]
  rw [he]
  exact old_signed_vector_mean_sq_le_positive Q f

/-- The analogous exact mean bound for the pure-first minus source. -/
theorem old_signed_pure_first_mean_norm_le_positive (Q : TriadicCube 2) (f : Vec 2 → Vec 2) :
    blockVecDot (oldSignedBlockMean Q (fun x => (f x,0)))
      (oldSignedBlockMean Q (fun x => (f x,0)))≤vectorPositiveHaarNorm Q f^2 := by
  have he : blockVecDot (oldSignedBlockMean Q (fun x => (f x,0)))
      (oldSignedBlockMean Q (fun x => (f x,0)))=∑ k : Fin 2,cubeAverage Q (fun x => f x k)^2 := by
    simp only [oldSignedBlockMean,blockVecDot,vecDot,Pi.zero_apply,cubeAverage_const,zero_mul,
      Finset.sum_const_zero,add_zero,pow_two]
  rw [he]
  exact old_signed_vector_mean_sq_le_positive Q f

/-- Every actual plus-flat cell-mean block has a summable complete square
series, including the source's negative second-block sign. -/
theorem old_signed_flat_plus_mean_series (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i : Fin 2) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n : whiteBasisIndex => blockVecDot
      (oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i))
      (oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i))) := by
  apply (old_signed_flat_plus_source_cell_energy_summable Q depth b L i U hU).of_nonneg_of_le
  · intro n
    exact add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  · intro n
    exact old_signed_pure_second_mean_norm_le_positive U _

/-- Every actual minus-flat cell-mean block has a summable complete
square series on the identical partition. -/
theorem old_signed_flat_minus_mean_series (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i : Fin 2) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n : whiteBasisIndex => blockVecDot
      (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i))
      (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i))) := by
  apply (old_signed_flat_minus_source_cell_energy_summable Q depth b L i U hU).of_nonneg_of_le
  · intro n
    exact add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  · intro n
    exact old_signed_pure_first_mean_norm_le_positive U _

end
end ASDExplicitGamma.Native
