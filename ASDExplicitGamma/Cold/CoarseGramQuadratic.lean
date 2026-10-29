module

public import ASDExplicitGamma.Cold.CoarseGramSign

/-! # Coarse duality and the sharp Gram quadratic bound for the actual square response -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open ASDExplicitGamma.Triadic
open scoped BigOperators RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- The square response is genuinely symmetric; the coarse-data witnesses are produced. -/
theorem coarse_square_full_isHermitian (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)).IsHermitian := by
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨sigma,hA,_,_,_,_,_,_⟩ := Variational.exists_energyMap_coarseData
    (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  have hs := (isCoarseBlockMatrix_coarseBlockMatrix ⟨_,hA⟩).1
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    isSymm_toFullBlockMat_of_isSymmetricBlockMat hs

/-- The actual swap involution in the Euclidean operator realization. -/
theorem coarseGramSwap_involutive (x : EuclideanSpace ℝ (BlockCoord 2)) :
    coarseGramSwap.toEuclideanLin (coarseGramSwap.toEuclideanLin x) = x := by
  have h := congrArg (fun B : FullBlockMat 2 => B.toEuclideanLin x) coarseGramSwap_sq
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one,
    LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Strict positivity follows from the two actual sign inequalities. -/
theorem coarse_square_full_posDef (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)).PosDef := by
  let A := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (coarse_square_full_isHermitian Q hEll)
  intro v hv
  have hne : WithLp.toLp 2 v ≠ (0 : EuclideanSpace ℝ (BlockCoord 2)) := by
    intro h
    apply hv
    exact congrArg WithLp.ofLp h
  have h := gram_positive_of_sign A.toEuclideanLin coarseGramSwap.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr coarseGramSwap_isHermitian)
    coarseGramSwap_involutive
    (fun x => (coarse_square_gram_signs Q hEll x).1)
    (fun x => (coarse_square_gram_signs Q hEll x).2) (WithLp.toLp 2 v) hne
  change 0 < ⟪WithLp.toLp 2 v,(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) A
    (WithLp.toLp 2 v)⟫ at h
  rw [matrix_euclidean_inner] at h
  exact h

/-- The actual square response satisfies inverse/reflection order, derived from its
variational sign inequalities. No duality hypothesis is left to the consumer. -/
theorem coarse_square_inverse_reflection_order (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (x : EuclideanSpace ℝ (BlockCoord 2)) :
    let A := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)
    ⟪x,A⁻¹.toEuclideanLin x⟫ ≤
      ⟪x,coarseGramSwap.toEuclideanLin (A.toEuclideanLin (coarseGramSwap.toEuclideanLin x))⟫ := by
  dsimp only
  let A := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)
  have hA := coarse_square_full_posDef Q hEll
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hTS (y : EuclideanSpace ℝ (BlockCoord 2)) : A.toEuclideanLin (A⁻¹.toEuclideanLin y) = y := by
    have h := congrArg (fun B : FullBlockMat 2 => B.toEuclideanLin y) (Matrix.mul_nonsing_inv A hdet)
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one,
      LinearMap.comp_apply, LinearMap.id_apply] using h
  exact gram_inverse_order_of_sign A.toEuclideanLin A⁻¹.toEuclideanLin coarseGramSwap.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr coarseGramSwap_isHermitian) hTS
    coarseGramSwap_involutive (fun y => (coarse_square_gram_signs Q hEll y).1)
    (fun y => (coarse_square_gram_signs Q hEll y).2) x

/-- The full response-plus-swap form has exactly the source P3 coefficient. -/
theorem coarse_square_gram_quadratic_le (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) {η : ℝ} (hη : 0 < η)
    (x : EuclideanSpace ℝ (BlockCoord 2)) :
    let A := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)
    ⟪x,A.toEuclideanLin x + coarseGramSwap.toEuclideanLin x⟫ ≤
      (2*(1+η)+(2+1/(4*η))*matrixGramDefect A coarseGramSwap)*⟪x,x⟫ := by
  dsimp only
  let A := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)
  have hA := coarse_square_full_posDef Q hEll
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hST (y : EuclideanSpace ℝ (BlockCoord 2)) : A⁻¹.toEuclideanLin (A.toEuclideanLin y) = y := by
    have h := congrArg (fun B : FullBlockMat 2 => B.toEuclideanLin y) (Matrix.nonsing_inv_mul A hdet)
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one,
      LinearMap.comp_apply, LinearMap.id_apply] using h
  have hp (y : EuclideanSpace ℝ (BlockCoord 2)) (hy : y ≠ 0) : 0 < ⟪y,A.toEuclideanLin y⟫ :=
    gram_positive_of_sign A.toEuclideanLin coarseGramSwap.toEuclideanLin
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr coarseGramSwap_isHermitian)
      coarseGramSwap_involutive (fun z => (coarse_square_gram_signs Q hEll z).1)
      (fun z => (coarse_square_gram_signs Q hEll z).2) y hy
  exact gram_reflection_quadratic_le
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) A)
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) A⁻¹)
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) coarseGramSwap)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian) hp hST
    (coarse_square_inverse_reflection_order Q hEll)
    (matrix_reflection_norm coarseGramSwap coarseGramSwap_isHermitian coarseGramSwap_sq) hη x

end ASDExplicitGamma.Cold
