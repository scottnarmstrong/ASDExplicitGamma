module

public import ASDExplicitGamma.Main.PartialInsertionSymmetry
public import ASDExplicitGamma.Variational.EnergyMap
public import Homogenization.CoarseGraining.OriginCubeSymmetry

/-! Pointwise response-matrix covariance for the actual partial insertion. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions

local instance mainAffineSymmetryFiniteMeasure (n : ℤ) :
    MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet (originCube 2 n))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isFiniteMeasure_restrict_volume

private theorem mainInsertion_partialCoarseWitness (M : ABKModel 2) (m n : ℤ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ Abar : BlockMat 2,
      IsCoarseBlockMatrix (openCubeSet (originCube 2 n))
        (Model.partialInsertedCoefficient M m t omega).toFun Abar := by
  let a := Model.partialInsertedCoefficient M m t omega
  have hEll : IsEllipticFieldOn M.nu
      (((2 : ℝ) * 2 * (Model.partialInsertedEntryBound M n m omega) ^ 2 +
        M.nu ^ 2) / M.nu)
      (openCubeSet (originCube 2 n)) a :=
    Model.partialInsertedCoefficient_isEllipticFieldOn M n m omega ht
      (measurableSet_openCubeSet (originCube 2 n)) (Set.Subset.rfl)
  have hvol : 0 <
      (MeasureTheory.volume (openCubeSet (originCube 2 n))).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube 2 n)
  obtain ⟨_, hCoarse, _, _, _, _, _, _⟩ :=
    exists_energyMap_coarseData
      (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) hEll hvol
  exact ⟨deterministicCoarseBlockMatrix (openCubeSet (originCube 2 n)) a.toFun,
    hCoarse⟩

private theorem mainInsertion_rotateCoefficient_toFun
    (a : RegCoeffField 2) (R : Mat 2) (hR : IsSignedPermutationMatrix R) :
    (Model.rotateCoefficientAbout (0 : Vec 2) R hR a).toFun =
      Homogenization.rotateCoeffField R a.toFun := by
  funext x
  apply Matrix.ext
  intro i j
  simp [Model.rotateCoefficientAbout_apply, Homogenization.rotateCoeffField]

/-- The actual partial-insertion coarse matrix transforms by signed
conjugation on an origin square. The matrix exists from the sample's actual
ellipticity; no coarse-matrix witness is supplied by the caller. -/
theorem mainInsertion_coarseBlockMatrix_signFlip (M : ABKModel 2)
    (m n : ℤ) (t : ℝ) (omega : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1) (i : Fin 2) :
    coarseBlockMatrix (openCubeSet (originCube 2 n))
        (Model.rotateCoefficientAbout (0 : Vec 2) (signFlipMatrix i)
          (isSignedPermutationMatrix_signFlipMatrix i)
          (Model.partialInsertedCoefficient M m t omega)).toFun =
      blockMatConj (signFlipMatrix i)
        (coarseBlockMatrix (openCubeSet (originCube 2 n))
          (Model.partialInsertedCoefficient M m t omega).toFun) := by
  let a := Model.partialInsertedCoefficient M m t omega
  have hrotate := mainInsertion_rotateCoefficient_toFun a (signFlipMatrix i)
    (isSignedPermutationMatrix_signFlipMatrix i)
  rw [hrotate]
  exact Homogenization.coarseBlockMatrix_signFlip_openCubeSet_originCube_of_exists
    (mainInsertion_partialCoarseWitness M m n t omega ht) i

/-- The same pointwise response-matrix covariance for a coordinate swap. -/
theorem mainInsertion_coarseBlockMatrix_swap (M : ABKModel 2)
    (m n : ℤ) (t : ℝ) (omega : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1) (i j : Fin 2) :
    coarseBlockMatrix (openCubeSet (originCube 2 n))
        (Model.rotateCoefficientAbout (0 : Vec 2) (Matrix.swap ℝ i j)
          (isSignedPermutationMatrix_swap i j)
          (Model.partialInsertedCoefficient M m t omega)).toFun =
      blockMatConj (Matrix.swap ℝ i j)
        (coarseBlockMatrix (openCubeSet (originCube 2 n))
          (Model.partialInsertedCoefficient M m t omega).toFun) := by
  let a := Model.partialInsertedCoefficient M m t omega
  have hrotate := mainInsertion_rotateCoefficient_toFun a (Matrix.swap ℝ i j)
    (isSignedPermutationMatrix_swap i j)
  rw [hrotate]
  exact Homogenization.coarseBlockMatrix_swap_openCubeSet_originCube_of_exists
    (mainInsertion_partialCoarseWitness M m n t omega ht) i j

end ASDExplicitGamma.Main

end
