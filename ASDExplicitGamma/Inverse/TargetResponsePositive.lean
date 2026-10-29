module

public import ASDExplicitGamma.Inverse.DescendantLinearCap
public import Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix

/-! Positivity of the genuine attenuated response on contained descendants. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The Book response is nonnegative for every pure-flux loading. -/
theorem book_pure_flux_nonneg (U : Book.Ch02.Domain 2) (a : Book.Ch02.CoeffOn U) (v : Vec 2) :
    0 ≤ dotProduct v ((Book.Ch02.coarseBlockMatrix U a).lowerRight.mulVec v) := by
  rw [lower_right_quadratic]
  by_cases hv : (0,v)=(0:BlockVec 2)
  · rw [hv]
    simp [blockVecDot,vecDot]
  · exact ((Book.Ch02.blockCoarseMatrixTheory U a).block_matrix_posDef _ hv).le

/-- The actual attenuated target has nonnegative local response on every
descendant. Its bounded continuous representative is constructed internally. -/
theorem attenuated_descendant_pure_flux_nonneg (M : ABKModel 2)
    {Q R : TriadicCube 2} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (n m J : ℤ) (hn : n ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (v : Vec 2) :
    0 ≤ dotProduct v ((coarseBlockMatrix (cubeSet R)
      (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) := by
  let k := oldResponseCoefficient Q n ω+
    laterResponseCoefficient Q n J (sourceBandWeights m weights) ω
  have hh := book_pure_flux_nonneg (Book.Ch02.cubeDomain R)
    (sensitivityBookCoeffOn R M.nu M.nu_pos (sensitivityResponseCoefficientRestrict k hR)) v
  rw [sensitivity_restrict_matrix_eq M.nu M.nu_pos k hR] at hh
  have he : coarseBlockMatrix (cubeSet R) (sensitivityBaseRegField M.nu k).toFun =
      coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with z hz
    exact sensitivity_path_represents_attenuated M Q n m J hn hm weights ω
      (openCubeSet_subset_of_mem_descendantsAtDepth hR hz)
  rwa [he] at hh

end
end ASDExplicitGamma.Inverse
