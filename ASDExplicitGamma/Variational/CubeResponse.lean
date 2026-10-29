module

public import ASDExplicitGamma.Variational.CubeOpen
public import ASDExplicitGamma.Variational.EnergyMap
public import Homogenization.CoarseGraining.MuRecoveryBlockResponse

/-! VA-RESP-IDENTITIES: the exact signed-load identity.
All recovery witnesses are produced by the existing convex-domain API. -/
@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory

/-- The source response identity on an elliptic open triadic cube. -/
theorem cube_response_quadratic {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec d) :
    ResponseJ (openCubeSet Q) p q a =
      (1/2 : ℝ)*blockVecDot (-p,q)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p,q))-vecDot p q := by
  have hConv := isOpenBoundedConvexDomain_openCubeSet Q
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have instFiniteOpenCubeVolume : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hConv.2.1.isFiniteMeasure_restrict_volume
  obtain ⟨R,sigma,compat,hA,_,_,_,_,_⟩ :=
    Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain hConv hEll hvol
  have hSplit := R.responseJ_eq_mu_neg_left_sub_vecDot_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    hConv hEll hvol compat p q
  have hcanon := isCoarseBlockMatrix_coarseBlockMatrix ⟨_,hA⟩
  rw [hSplit,hcanon.2 (-p,q)]

/-- The same coefficient and response identity on every descendant at a fixed depth. -/
theorem cube_response_quadratic_descendants {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    ∀ R ∈ descendantsAtDepth Q j, ∀ p q : Vec d,
      ResponseJ (openCubeSet R) p q a =
        (1/2 : ℝ)*blockVecDot (-p,q)
          (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p,q))-vecDot p q := by
  intro R hR p q
  exact cube_response_quadratic R a
    (hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_of_mem_descendantsAtDepth hR)) p q

/-- The same identity on the frozen half-open cube, transported without altering the load. -/
theorem cube_response_quadratic_halfOpen {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec d) :
    ResponseJ (cubeSet Q) p q a =
      (1/2 : ℝ)*blockVecDot (-p,q)
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) (-p,q))-vecDot p q := by
  rw [cube_response_eq_open,cube_coarseMatrix_eq_open]
  exact cube_response_quadratic Q a hEll p q

end ASDExplicitGamma.Variational
