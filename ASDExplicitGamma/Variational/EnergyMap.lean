module

public import Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimates
public import Homogenization.Internal.Ch02.DoubledMu

/-!
# Coarse data and the nonsymmetric energy map

The old deterministic data are produced from domain geometry and ellipticity.
No recovery or matrix-identification witnesses are assumptions of the estimates.
-/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization
open Homogenization.Book Homogenization.Book.Ch02

/-- VA-ENERGYMAP-DATA: all deterministic coarse-data witnesses, including
positive definiteness and the unit determinant, follow from source premises. -/
theorem exists_energyMap_coarseData {d : ℕ} [NeZero d] {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ∃ sigma : Mat d,
      IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a) ∧
      IsSigmaStarInvCoarse U a (sigmaStarInvCoarse U a) ∧
      IsSigmaStarCoarse U a (sigmaStarCoarse U a) ∧
      IsKappaCoarse U a (sigmaStarCoarse U a) (kappaCoarse U a) ∧
      IsSigmaCoarse U a sigma (sigmaStarCoarse U a) (kappaCoarse U a) ∧
      (sigmaStarInvCoarse U a).PosDef ∧ IsUnit (sigmaStarCoarse U a).det := by
  obtain ⟨R, sigma, compat, hA, hSInv, hS, hK, hSigma, _⟩ :=
    Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      hConv hEll hvol
  exact ⟨sigma, hA, hSInv, hS, hK, hSigma,
    sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      R hConv hEll hvol compat,
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      R hConv hEll hvol compat hS⟩

/-- The Book coarse block equals the public variational coarse block, with
all matrix-data witnesses discharged by the domain producer. -/
theorem energyMap_coarseBlockMatrix_eq {d : ℕ} [NeZero d]
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    Ch02.coarseBlockMatrix U a =
      Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField := by
  obtain ⟨sigma, hA, _, hS, hK, hSigma, _, hdet⟩ :=
    exists_energyMap_coarseData U.isDomain hEll (Internal.Ch02.BookCh02.domain_volume_pos U)
  exact Internal.Ch02.BookCh02.book_coarseBlockMatrix_eq_old_coarseBlockMatrix_of_data
    U a hA hS hK hSigma hdet

/-- VA-ENERGYMAP, expressed using the lower-right block of the public coarse
matrix rather than an unidentified Book matrix. -/
theorem vecNormSq_averageGradient_le_coarseBlockMatrix_mul_energy
    {d : ℕ} [NeZero d] (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (w : Solution U a) :
    vecNormSq (Ch02.averageGradient U a w) ≤
      matrixNorm (Homogenization.coarseBlockMatrix
        (U : Set (Vec d)) a.toCoeffField).lowerRight *
      Ch02.variationEnergyValue U a w := by
  have hblock := energyMap_coarseBlockMatrix_eq U a hEll
  have hright := congrArg BlockMat.lowerRight hblock
  have henergy :=
    Ch02.vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue
      U a w
  rw [← hright]
  exact henergy

end ASDExplicitGamma.Variational
