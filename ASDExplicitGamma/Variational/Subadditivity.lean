module

public import ASDExplicitGamma.Variational.CubeResponse
public import ASDExplicitGamma.Variational.TraceDefect
public import Homogenization.CoarseGraining.Subadditivity

/-! VA-SUBADDITIVITY. The response-identity premises of the upstream block theorem
are discharged by CubeResponse on the parent and the actual descendants. -/
@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization Algsuperdiff.Section3

theorem cube_response_subadditive {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec d) :
    ResponseJ (openCubeSet Q) p q a ≤
      descendantsAverage Q 1 (fun R => ResponseJ (openCubeSet R) p q a) :=
  responseJ_subadditive_openCubeSet_childCubes_of_isEllipticFieldOn Q a hEll p q

theorem cube_coarse_matrix_subadditive {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (j : ℕ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    BlockMatLoewnerLE (coarseBlockMatrix (openCubeSet Q) a)
      (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (openCubeSet R) a)) :=
  coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_responseJ_blockQuadratic
    j Q a hEll (cube_response_quadratic Q a hEll) (cube_response_quadratic_descendants Q j a hEll)

theorem cube_coarse_matrix_subadditive_halfOpen {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (j : ℕ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    BlockMatLoewnerLE (coarseBlockMatrix (cubeSet Q) a)
      (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a)) := by
  simpa only [cube_coarseMatrix_eq_open] using cube_coarse_matrix_subadditive Q j a hEll

/-- The actual completed cutoff needs no additional ellipticity or identity premise. -/
theorem cutoff_coarse_matrix_subadditive (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    BlockMatLoewnerLE (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)
      (descendantsAverageBlockMat Q j
        (fun R => coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun)) := by
  obtain ⟨Λ,hEll⟩ := cutoff_isEllipticFieldOn_cube M n ω Q
  exact cube_coarse_matrix_subadditive_halfOpen Q j _
    (hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q))

end ASDExplicitGamma.Variational
