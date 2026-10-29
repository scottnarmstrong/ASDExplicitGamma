module

public import ASDExplicitGamma.Scalar.CellResponseTest

/-! Polarization and first variation recover the actual coarse response from
constant tests of the canonical affine minimizer. No sign of a partial-law
expected coarse block is used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Variational
noncomputable section

/-- Constant testing equals testing against the other genuine minimizer.
This is an exact first-variation identity, before any covariance estimate. -/
theorem old_signed_minimizer_constant_pairing {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} (M : MuHilbertRealization U a) (P R : BlockVec d) :
    M.energyBilin (M.minimizerMap P) (M.constantField R) =
      M.energyBilin (M.minimizerMap P) (M.minimizerMap R) := by
  have h := M.minimizerMap_firstVariation P
    ⟨M.minimizerMap R-M.constantField R,M.sub_minimizerMap_apply_mem R⟩
  change M.energyBilin (M.minimizerMap P) (M.minimizerMap R-M.constantField R)=0 at h
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

/-- Polarization of the genuine minimized quadratic energy; this helper does
not replace the physical coarse-matrix identification below. -/
theorem old_signed_minimizer_polarization {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} (M : MuHilbertRealization U a) (P R : BlockVec d) :
    M.energyBilin (M.minimizerMap P) (M.minimizerMap R) =
      M.muCandidate (P+R)-M.muCandidate P-M.muCandidate R := by
  change _ = quadraticEnergy M.energyBilin (M.minimizerMap (P+R))-
    quadraticEnergy M.energyBilin (M.minimizerMap P)-
    quadraticEnergy M.energyBilin (M.minimizerMap R)
  rw [map_add]
  simp only [quadraticEnergy,map_add,add_apply]
  rw [M.energySymm (M.minimizerMap R) (M.minimizerMap P)]
  ring

/-- The actual canonical Hilbert minimizer, on the same source square, has
constant-test pairing equal to the physical coarse block bilinear form. -/
theorem old_signed_canonical_constant_pairing (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P R : BlockVec 2) :
    let M := (scalarCellSystem Q a hEll).toMuHilbertRealization
    M.energyBilin (M.minimizerMap P) (M.constantField R) =
      blockVecDot R (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) := by
  intro M
  rw [old_signed_minimizer_constant_pairing,old_signed_minimizer_polarization]
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hm (X : BlockVec 2) : M.muCandidate X=Mu (openCubeSet Q) X a :=
    lemmaV_canonical_muCandidate_eq_Mu (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol X
  rw [hm,hm,hm]
  obtain ⟨A,S,K,hA,_,_,_,_,_⟩ :=
    Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  have hq (X : BlockVec 2) : Mu (openCubeSet Q) X a =
      (1/2:ℝ)*blockVecDot X (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) X) := by
    simpa only [eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA] using hA.2 X
  rw [hq,hq,hq]
  simp only [blockMatVecMul_add,blockVecDot_add_left,blockVecDot_add_right]
  rw [blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat
    (coarseBlockMatrix_symmetric (openCubeSet Q) a) P R]
  ring

end
end ASDExplicitGamma.Native
