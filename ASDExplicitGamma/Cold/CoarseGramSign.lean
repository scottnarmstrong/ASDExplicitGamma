module

public import ASDExplicitGamma.Cold.GramMatrix
public import ASDExplicitGamma.Cold.PlateauTransportWeights
public import ASDExplicitGamma.Variational.EnergyMap
public import Homogenization.CoarseGraining.MuAdmissibility
public import Homogenization.CoarseGraining.ResponseIdentities.Existence

/-! # Actual coarse response sign inequalities on the square -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- The literal block-swap matrix on the doubled planar space. -/
def coarseGramSwap : FullBlockMat 2 := toFullBlockMat (Book.Ch02.blockR 2)

/-- The literal swap acts by interchanging the two loads. -/
theorem coarseGramSwap_mulVec (P : BlockVec 2) :
    coarseGramSwap.mulVec (toFullBlockVec P) = toFullBlockVec (P.2,P.1) := by
  ext i
  cases i <;> simp [coarseGramSwap, toFullBlockMat, Book.Ch02.blockR, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, toFullBlockVec, Matrix.one_apply]

/-- Symmetry of the actual load swap. -/
theorem coarseGramSwap_isHermitian : coarseGramSwap.IsHermitian := by
  change coarseGramSwap.conjTranspose = coarseGramSwap
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.conjTranspose_apply, coarseGramSwap, toFullBlockMat, Book.Ch02.blockR, Matrix.one_apply, eq_comm]

/-- The actual swap is an involution. -/
theorem coarseGramSwap_sq : coarseGramSwap * coarseGramSwap = 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [coarseGramSwap, toFullBlockMat, Book.Ch02.blockR, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply]

/-- The Euclidean quadratic form is the ordinary full-matrix quadratic form. -/
theorem matrix_euclidean_inner (B : FullBlockMat 2) (x : EuclideanSpace ℝ (BlockCoord 2)) :
    ⟪x,(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) B x⟫ = x.ofLp ⬝ᵥ (B.mulVec x.ofLp) := by
  change ⟪x,B.toEuclideanLin x⟫ = _
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, star_trivial, dotProduct_comm]

/-- The actual coarse quadratic representation, with all recovery data discharged. -/
theorem coarse_square_response_quadratic (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec 2) :
    ResponseJ (openCubeSet Q) p q a =
      (1/2 : ℝ) * blockVecDot (-p,q)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p,q)) - vecDot p q := by
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨sigma, hA, _, hS, hK, hSigma, _, hdet⟩ :=
    Variational.exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  exact magic_identity_responseJ_block_quadratic_coarseBlockMatrix_of_isSigmaCoarse
    (openCubeSet Q) a hA hS hK hSigma hdet p q

/-- The actual variational coarse matrix satisfies both sign inequalities. -/
theorem coarse_square_gram_signs (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (x : EuclideanSpace ℝ (BlockCoord 2)) :
    let A := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2))
      (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a))
    let R := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) coarseGramSwap
    0 ≤ ⟪x,A x + R x⟫ ∧ 0 ≤ ⟪x,A x - R x⟫ := by
  dsimp only
  let P : BlockVec 2 := ofFullBlockVec x.ofLp
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨sigma, hA, _, _, _, _, _, _⟩ :=
    Variational.exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  have hcoarse := isCoarseBlockMatrix_coarseBlockMatrix ⟨_, hA⟩
  have hMu := hcoarse.2 P
  have hJ := coarse_square_response_quadratic Q hEll (-P.1) P.2
  simp only [neg_neg, vecDot_neg_left] at hJ
  have hJn := responseJ_nonneg (openCubeSet Q) (-P.1) P.2 a
  have hMule := IsBlockMuAdmissible.mu_ge_vecDot_of_isEllipticFieldOn_of_isSobolevRegularDomain
    (P := P) (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain hEll hvol.ne'
  have hAx : ⟪x,(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2))
      (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)) x⟫ =
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) := by
    rw [matrix_euclidean_inner]
    rw [show x.ofLp = toFullBlockVec P by simp [P],
      ← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]
  have hRx : ⟪x,(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) coarseGramSwap x⟫ =
      2 * vecDot P.1 P.2 := by
    rw [matrix_euclidean_inner, show x.ofLp = toFullBlockVec P by simp [P],
      coarseGramSwap_mulVec, dotProduct_toFullBlockVec]
    simp only [blockVecDot, vecDot_comm P.2 P.1]
    ring
  rw [inner_add_right, inner_sub_right, hAx, hRx]
  constructor <;> linarith only [hMu,hMule,hJ,hJn]

end ASDExplicitGamma.Cold
