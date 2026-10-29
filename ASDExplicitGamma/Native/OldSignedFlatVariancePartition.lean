module

public import ASDExplicitGamma.Native.OldSignedFlatVarianceModes
public import ASDExplicitGamma.Native.OldSignedPartitionSeries
public import ASDExplicitGamma.Native.OldSignedPairedProjectionTrace

/-! Sharp cell Poincaré payment of the complete OLD affine mean loss. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Main
noncomputable section

/-- The actual whole-partition loss from replacing the flat modes by cell means. -/
def oldSignedFlatMeanLoss (Q : TriadicCube 2) (r : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) : ℝ :=
  descendantsAverage Q r (fun U => oldSignedFlatL2Size Q U b L plus^2-oldSignedFlatMeanSize Q U b L plus^2)

/-- The exact mean loss is nonnegative, without taking a positive part. -/
theorem old_signed_flat_mean_loss_nonneg (Q : TriadicCube 2) (r : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) : 0≤oldSignedFlatMeanLoss Q r b L plus := by
  apply descendantsAverage_nonneg
  intro U hU
  exact sub_nonneg.mpr (pow_le_pow_left₀ (Real.sqrt_nonneg _)
    (old_signed_flat_mean_size_le_l2 Q r b L plus U hU) 2)

/-- The literal cell mean energy is the full parent energy minus its exact
whole-partition variance. -/
theorem old_signed_flat_mean_partition_identity (Q : TriadicCube 2) (r : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    descendantsAverage Q r (fun U => oldSignedFlatMeanSize Q U b L plus^2)=
      oldSignedFlatL2Size Q Q b L plus^2-oldSignedFlatMeanLoss Q r b L plus := by
  unfold oldSignedFlatMeanLoss
  rw [old_signed_descendants_average_sub,old_signed_flat_l2_size_partition]
  ring

/-- The complete covariance variance pays the sharp cell Poincaré factor,
with the physical shell length left arbitrary. -/
theorem old_signed_flat_mean_loss_gradient_cap (Q : TriadicCube 2) (r : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    oldSignedFlatMeanLoss Q r b L plus≤
      (cubeScaleFactor Q/(Real.pi*3^r))^2*((if plus then (1+Real.sqrt 2)^2 else 1)*mainFlatSigmaSq b L) := by
  let F := fun n : whiteBasisIndex => if plus then mainFlatPlusH1 Q b L n else mainFlatMinusH1 Q b L n
  let f := fun n U => hilbertEnergy U (fun x => (F n).toFun x-hilbertCubeAverage U (F n).toFun)
  have hgrad : Summable (fun n => hilbertGradientEnergy Q (F n).grad) ∧
      (∑' n,hilbertGradientEnergy Q (F n).grad)≤(if plus then (1+Real.sqrt 2)^2 else 1)*mainFlatSigmaSq b L := by
    cases plus
    · simp only [F,Bool.false_eq_true,ite_false,one_mul]
      exact ⟨(mainFlatMinusGradientEnergy_tsum Q b L).1,(mainFlatMinusGradientEnergy_tsum Q b L).2.le⟩
    · simpa only [F,ite_true] using mainFlatPlusGradientEnergy_tsum Q b L
  have hmode (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r) (n : whiteBasisIndex) :
      (∑ i : Fin 2,oldSignedBlockL2Energy U (oldSignedFlatInput Q b L plus n i))-
        (∑ i : Fin 2,blockVecDot (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i))
          (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)))=f n U := by
    rw [←Finset.sum_sub_distrib]
    cases plus
    · exact old_signed_flat_minus_mode_variance Q r U hU b L n
    · exact old_signed_flat_plus_mode_variance Q r U hU b L n
  have hs (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r) : Summable (fun n => f n U) :=
    ((old_signed_flat_l2_budget_series Q r b L plus U hU).sub
      (old_signed_flat_mean_budget_series Q r b L plus U hU)).congr (hmode U hU)
  have he (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r) :
      oldSignedFlatL2Size Q U b L plus^2-oldSignedFlatMeanSize Q U b L plus^2=∑' n,f n U := by
    rw [old_signed_flat_l2_size_sq,old_signed_flat_mean_size_sq,
      ←(old_signed_flat_l2_budget_series Q r b L plus U hU).tsum_sub
        (old_signed_flat_mean_budget_series Q r b L plus U hU)]
    exact tsum_congr (hmode U hU)
  have hpart : oldSignedFlatMeanLoss Q r b L plus=∑' n,descendantsAverage Q r (f n) := by
    rw [(old_signed_partition_series Q r f hs).2]
    unfold oldSignedFlatMeanLoss descendantsAverage
    dsimp only
    congr 1
    exact Finset.sum_congr rfl (fun U hU => he U hU)
  rw [hpart]
  have hh := main_hilbert_cell_variance_le_gradient_tsum Q r F hgrad.1
  exact hh.2.trans (mul_le_mul_of_nonneg_left hgrad.2 (sq_nonneg _))

end
end ASDExplicitGamma.Native
