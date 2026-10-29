module

public import ASDExplicitGamma.Cold.CoarseGramQuadratic
public import ASDExplicitGamma.Cold.SquareCellMean
public import Homogenization.CoarseGraining.MagicIdentities.BlockSubadditivity

/-! # Actual full-response subadditivity with all coarse witnesses discharged -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The literal full matrix of averaged actual child responses. -/
def squareResponseAverage (Q : TriadicCube 2) (r : ℕ) (a : CoeffField 2) : FullBlockMat 2 :=
  fun i j => squareCellMean Q r (fun C => toFullBlockMat (coarseBlockMatrix (openCubeSet C.val) a) i j)

theorem squareResponseAverage_eq (Q : TriadicCube 2) (r : ℕ) (a : CoeffField 2) :
    squareResponseAverage Q r a =
      toFullBlockMat (descendantsAverageBlockMat Q r (fun R => coarseBlockMatrix (openCubeSet R) a)) := by
  have hm (f : TriadicCube 2 → ℝ) : squareCellMean Q r (fun C => f C.val) = descendantsAverage Q r f := by
    unfold squareCellMean descendantsAverage
    congr 1
    exact Finset.sum_attach (descendantsAtDepth Q r) f
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hm (fun R => (coarseBlockMatrix (openCubeSet R) a).upperLeft i j)
    | inr j => exact hm (fun R => (coarseBlockMatrix (openCubeSet R) a).upperRight i j)
  | inr i =>
    cases j with
    | inl j => exact hm (fun R => (coarseBlockMatrix (openCubeSet R) a).lowerLeft i j)
    | inr j => exact hm (fun R => (coarseBlockMatrix (openCubeSet R) a).lowerRight i j)


/-- Symmetry of the literal child average follows from actual cell ellipticity. -/
theorem squareResponseAverage_isHermitian (Q : TriadicCube 2) (r : ℕ) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) : (squareResponseAverage Q r a).IsHermitian := by
  change (squareResponseAverage Q r a).conjTranspose = squareResponseAverage Q r a
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial]
  unfold squareResponseAverage
  congr 1
  funext C
  exact (coarse_square_full_isHermitian C.val
    (hEll.mono (measurableSet_openCubeSet C.val) (openCubeSet_subset_of_mem_descendantsAtDepth C.property))).isSymm.apply i j

/-- The actual parent lies below its full matrix child average in Loewner order. -/
theorem square_response_subadditive (Q : TriadicCube 2) (r : ℕ) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    (squareResponseAverage Q r a-toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)).PosSemidef := by
  have hex (R : TriadicCube 2) (hR : IsEllipticFieldOn lam Lam (openCubeSet R) a) :=
    Variational.exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet R) hR
      (by rw [volume_openCubeSet_eq_volume_cubeSet,volume_cubeSet_toReal]; exact cubeVolume_pos R)
  obtain ⟨σ,hA,_,hS,hK,hSigma,_,hdet⟩ := hex Q hEll
  have hd : ∀ R ∈ descendantsAtDepth Q r, ∃ σR σSR κR,
      IsCoarseBlockMatrix (openCubeSet R) a (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
      IsSigmaStarCoarse (openCubeSet R) a σSR ∧ IsKappaCoarse (openCubeSet R) a σSR κR ∧
      IsSigmaCoarse (openCubeSet R) a σR σSR κR ∧ IsUnit σSR.det := by
    intro R hR
    obtain ⟨σR,hAR,_,hSR,hKR,hSigmaR,_,hdetR⟩ := hex R
      (hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_of_mem_descendantsAtDepth hR))
    exact ⟨σR,_,_,hAR,hSR,hKR,hSigmaR,hdetR⟩
  have ho := coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
    r Q a hEll hA hS hK hSigma hdet hd
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((squareResponseAverage_isHermitian Q r hEll).sub (coarse_square_full_isHermitian Q hEll))
  intro x
  have hh := ho (ofFullBlockVec x)
  simp only [← dotProduct_toFullBlockVec,toFullBlockVec_blockMatVecMul,toFullBlockVec_ofFullBlockVec] at hh
  rw [← squareResponseAverage_eq] at hh
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub]
  linarith only [hh]

end ASDExplicitGamma.Cold
