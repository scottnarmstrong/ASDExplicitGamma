module

public import ASDExplicitGamma.Inverse.GoodCellResponse
public import ASDExplicitGamma.Inverse.ContainedTriangleRootResponse

/-! Literal coefficient restrictions for the actual hybrid variational cells. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- Restricting the genuine sensitivity coefficient to any convex observation
subdomain gives the public coarse matrix of that same physical field. -/
theorem sensitivity_domain_matrix_eq (Q : TriadicCube 2) (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient (openCubeSet Q)) (V : Book.Ch02.Domain 2)
    (hV : (V:Set (Vec 2)) ⊆ openCubeSet Q) :
    Book.Ch02.coarseBlockMatrix V (restrictCoeffOn (sensitivityBookCoeffOn Q ν hν k) hV) =
      coarseBlockMatrix (V:Set (Vec 2)) (sensitivityBaseRegField ν k).toFun := by
  have hEll : IsEllipticFieldOn (sensitivityBookCoeffOn Q ν hν k).lam
      (sensitivityBookCoeffOn Q ν hν k).Lam (openCubeSet Q)
      (sensitivityBookCoeffOn Q ν hν k).toCoeffField := by
    simpa [sensitivityBookCoeffOn,div_one] using
      responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν 1 hν one_pos k
  exact ASDExplicitGamma.Variational.energyMap_coarseBlockMatrix_eq V _ (hEll.mono V.measurableSet hV)

/-- The literal old-plus-band restriction has the actual attenuated target
matrix on every physical hybrid cell, regardless of its Tietze extension. -/
theorem attenuated_domain_matrix_eq (M : ABKModel 2) (Q : TriadicCube 2)
    (n m J : ℤ) (hn : n ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (V : Book.Ch02.Domain 2) (hV : (V:Set (Vec 2)) ⊆ openCubeSet Q) :
    Book.Ch02.coarseBlockMatrix V (restrictCoeffOn (sensitivityBookCoeffOn Q M.nu M.nu_pos
      (oldResponseCoefficient Q n ω+laterResponseCoefficient Q n J (sourceBandWeights m weights) ω)) hV) =
      coarseBlockMatrix (V:Set (Vec 2)) (attenuatedCoefficient M m J weights ω) := by
  rw [sensitivity_domain_matrix_eq]
  apply coarseBlockMatrix_congr_of_ae_eq
  filter_upwards [ae_restrict_mem V.measurableSet] with x hx
  exact sensitivity_path_represents_attenuated M Q n m J hn hm weights ω (hV hx)

end
end ASDExplicitGamma.Inverse
