module

public import ASDExplicitGamma.Inverse.StoppedElementaryCubes
public import Homogenization.Geometry.CubeMetric

/-! Actual elementary observations fit in the complete physical restriction carrier. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Gaussian
noncomputable section

theorem physical_block_side_eq (j : ℤ) :
    physicalBlockSide j = 2*(3:ℝ)^40*(3:ℝ)^j := by
  unfold physicalBlockSide
  rw [zpow_add₀ (by norm_num : (3:ℝ) ≠ 0)]
  norm_num only [zpow_ofNat]
  ring

theorem buffered_parent_index_bounds (j : ℤ) (x : BlockSite)
    (i : BufferedParentIndex) (d : Fin 2) :
    2*(3^40:ℤ)*x d ≤ (bufferedParent j x i).index d ∧
    (bufferedParent j x i).index d+1 ≤ 2*(3^40:ℤ)*(x d+1) := by
  have hcorner := i.1.isLt
  have hfirst := i.2.1.isLt
  have hsecond := i.2.2.isLt
  have hmod : i.1.val%2 < 2 := Nat.mod_lt _ (by norm_num)
  fin_cases d <;> simp only [bufferedParent,Fin.reduceFinMk,ite_true,Fin.zero_eta,Fin.isValue] <;>
    norm_num at * <;> omega

theorem buffered_parent_contained (j : ℤ) (x : BlockSite) (i : BufferedParentIndex) :
    cubeSet (bufferedParent j x i) ⊆ physicalBlockRegion j x 1 := by
  intro p hp d
  have hidx := buffered_parent_index_bounds j x i d
  have hlow : 2*(3:ℝ)^40*(x d:ℝ) ≤ ((bufferedParent j x i).index d:ℝ) := by
    exact_mod_cast hidx.1
  have hupp : ((bufferedParent j x i).index d:ℝ)+1 ≤ 2*(3:ℝ)^40*((x d:ℝ)+1) := by
    exact_mod_cast hidx.2
  have hL : 0 ≤ (3:ℝ)^j := (zpow_pos (by norm_num) _).le
  have hl := mul_le_mul_of_nonneg_right hlow hL
  have hu := mul_le_mul_of_nonneg_right hupp hL
  have hp' := hp d
  change (((bufferedParent j x i).index d:ℝ)-1/2)*(3:ℝ)^j ≤ p d ∧
    p d < (((bufferedParent j x i).index d:ℝ)+1/2)*(3:ℝ)^j at hp'
  change physicalBlockSide j*(x d:ℝ)-(3:ℝ)^j/2 ≤ p d ∧
    p d ≤ physicalBlockSide j*((x d:ℝ)+(1:ℕ))-(3:ℝ)^j/2
  norm_num only [Nat.cast_one]
  rw [physical_block_side_eq]
  constructor <;> nlinarith only [hp'.1,hp'.2,hl,hu]

theorem physical_block_region_closed (j : ℤ) (a : BlockSite) (s : ℕ) :
    IsClosed (physicalBlockRegion j a s) := by
  have hi (d : Fin 2) : IsClosed {x : Vec 2 |
      physicalBlockSide j*(a d:ℝ)-(3:ℝ)^j/2 ≤ x d ∧
      x d ≤ physicalBlockSide j*((a d:ℝ)+s)-(3:ℝ)^j/2} :=
    (isClosed_le continuous_const (continuous_apply d)).inter
      (isClosed_le (continuous_apply d) continuous_const)
  simpa only [physicalBlockRegion,Set.iInter_ofPred] using isClosed_iInter hi

/-- Passing to the full closed observation square costs no enlargement. -/
theorem closed_square_subset_of_cube_subset {Q : TriadicCube 2} {U : Set (Vec 2)}
    (hU : IsClosed U) (hQ : cubeSet Q ⊆ U) :
    supMeanClosedSquare (cubeCenter Q) (cubeScaleFactor Q) ⊆ U := by
  have hs : supMeanClosedSquare (cubeCenter Q) (cubeScaleFactor Q) =
      Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
    ext p
    rw [Metric.mem_closedBall,dist_eq_norm,pi_norm_le_iff_of_nonneg (cubeRadius_nonneg Q)]
    change (∀ d, |p d-cubeCenter Q d| ≤ cubeScaleFactor Q/2) ↔
      (∀ d, |p d-cubeCenter Q d| ≤ (1/2:ℝ)*cubeScaleFactor Q)
    simp only [div_eq_mul_inv,mul_comm,one_mul]
  rw [hs,← closure_ball _ (cubeRadius_pos Q).ne']
  apply closure_minimal _ hU
  rw [ball_cubeCenter_eq_openCubeSet]
  exact (openCubeSet_subset_cubeSet Q).trans hQ

/-- All parent and descendant jets and their boundary suprema observe only
this one source block; smaller descendants introduce no neighbor inflation. -/
theorem elementary_closed_square_contained (j : ℤ) (x : BlockSite)
    (i : WavePlanarElementaryIndex) :
    supMeanClosedSquare (cubeCenter (elementaryCube j x i))
      (cubeScaleFactor (elementaryCube j x i)) ⊆ physicalBlockRegion j x 1 := by
  apply closed_square_subset_of_cube_subset (physical_block_region_closed j x 1)
  exact (cubeSet_subset_of_mem_descendantsAtDepth (elementary_cube_mem j x i)).trans
    (buffered_parent_contained j x (i.1,i.2.1))

end
end ASDExplicitGamma.Inverse
