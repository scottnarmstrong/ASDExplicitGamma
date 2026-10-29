module

public import ASDExplicitGamma.Native.ParentBoundaryFlatMeanGeometry
public import ASDExplicitGamma.Native.OldSignedPartitionSeries
public import ASDExplicitGamma.Native.OldSignedPureSecondPairing
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedLoadSeriesBudget
public import ASDExplicitGamma.Native.OldSignedAffineContribution
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport

/-! Exact complete flat mean loss and its sharp deterministic charge. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic
noncomputable section

/-- The actual complete mean norm square is its nonnegative mode series. -/
theorem parent_boundary_flat_mean_size_sq (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    oldSignedFlatMeanSize Q U b L plus^2=
      ∑' i : whiteBasisIndex,∑ col : Fin 2,blockVecDot
        (oldSignedBlockMean U (oldSignedFlatInput Q b L plus i col))
        (oldSignedBlockMean U (oldSignedFlatInput Q b L plus i col)) := by
  apply Real.sq_sqrt
  exact tsum_nonneg (fun i => Finset.sum_nonneg (fun col _ =>
    add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)))

/-- The complete actual cell-mean loss equals the SAME physical Hilbert
variance. Infinite covariance sums commute with the finite partition only
after their genuine convergence has been proved. -/
theorem parent_boundary_flat_mean_loss (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    oldSignedFlatL2Size Q Q b L plus^2-
      descendantsAverage Q depth (fun U => oldSignedFlatMeanSize Q U b L plus^2)=
      parentBoundaryFlatVariance Q depth b L plus := by
  let F := fun i U => ∑ col : Fin 2,oldSignedBlockL2Energy U (oldSignedFlatInput Q b L plus i col)
  let G := fun i U => ∑ col : Fin 2,blockVecDot
    (oldSignedBlockMean U (oldSignedFlatInput Q b L plus i col))
    (oldSignedBlockMean U (oldSignedFlatInput Q b L plus i col))
  have hsF (U) (hU : U∈descendantsAtDepth Q depth) : Summable (fun i => F i U) :=
    old_signed_flat_l2_budget_series Q depth b L plus U hU
  have hsG (U) (hU : U∈descendantsAtDepth Q depth) : Summable (fun i => G i U) :=
    old_signed_flat_mean_budget_series Q depth b L plus U hU
  have hcell (U) (hU : U∈descendantsAtDepth Q depth) :
      oldSignedFlatL2Size Q U b L plus^2-oldSignedFlatMeanSize Q U b L plus^2=
        ∑' i,(F i U-G i U) := by
    rw [old_signed_flat_l2_size_sq,parent_boundary_flat_mean_size_sq]
    exact ((hsF U hU).tsum_sub (hsG U hU)).symm
  have hh := old_signed_partition_series Q depth (fun i U => F i U-G i U)
    (fun U hU => (hsF U hU).sub (hsG U hU))
  have he : descendantsAverage Q depth (fun U =>
      oldSignedFlatL2Size Q U b L plus^2-oldSignedFlatMeanSize Q U b L plus^2)=
      descendantsAverage Q depth (fun U => ∑' i,(F i U-G i U)) := by
    unfold descendantsAverage
    dsimp only
    congr 1
    exact Finset.sum_congr rfl hcell
  rw [←old_signed_flat_l2_size_partition Q depth b L plus,←old_signed_descendants_average_sub,he,←hh.2]
  unfold parentBoundaryFlatVariance
  apply tsum_congr
  intro i
  unfold descendantsAverage
  dsimp only
  congr 1
  exact Finset.sum_congr rfl (fun U hU => parent_boundary_flat_cell_mean_loss Q depth U hU b L plus i)

/-- The complete two-family loss in the signed affine expectation is paid
by exactly the sharp source cell-variance constant. -/
theorem parent_boundary_joint_flat_mean_loss_bound (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    (oldSignedFlatL2Size Q Q b L true^2-descendantsAverage Q depth (fun U => oldSignedFlatMeanSize Q U b L true^2))+
      (oldSignedFlatL2Size Q Q b L false^2-descendantsAverage Q depth (fun U => oldSignedFlatMeanSize Q U b L false^2))≤
      (4+2*Real.sqrt 2)*(cubeScaleFactor Q/(Real.pi*(3:ℝ)^depth))^2*mainFlatSigmaSq b L := by
  rw [parent_boundary_flat_mean_loss,parent_boundary_flat_mean_loss]
  exact parent_boundary_joint_flat_variance_bound Q depth b L

end
end ASDExplicitGamma.Native
