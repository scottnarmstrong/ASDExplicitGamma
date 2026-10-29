module

public import ASDExplicitGamma.Native.ParentBoundaryBandRegular
public import ASDExplicitGamma.Scalar.CellTranslation
public import Homogenization.CoarseGraining.OriginCubeSymmetry

/-! Actual finite-band coarse matrices: measurable entries, physical
translation, and the exact coordinate symmetries on origin squares. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open Response Scalar Triadic Variational Inverse
noncomputable section

/-- Every full coarse entry of the actual finite weighted band is measurable. -/
theorem parent_boundary_band_full_coarse_measurable (M : ABKModel 2) (n J : ℤ)
    (weights : ℤ → ℝ) (Q : TriadicCube 2) :
    Measurable (fun omega : Cutoff.CutoffSample 2 => toFullBlockMat
      (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M n J weights omega))) := by
  classical
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := parentBoundaryBandRegCoefficient M n J weights
  have hX : Measurable X := parent_boundary_band_reg_measurable M n J weights
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) :=
    fun ω => parent_boundary_band_locally_elliptic M n J weights ω
  have heq : (fun omega : Cutoff.CutoffSample 2 => toFullBlockMat
      (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M n J weights omega)))=
      (fun omega => toFullBlockMat (coarseBlockMatrix (cubeSet Q) (X omega).toFun)) := by
    funext omega
    apply congrArg (fun a : CoeffField 2 => toFullBlockMat (coarseBlockMatrix (cubeSet Q) a))
    funext x
    exact (parent_boundary_band_reg_apply M n J weights omega x).symm
  rw [heq]
  have hmu (P : BlockVec 2) :=
    Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_Mu_cubeSet hX hEll Q P
  have he (α β : BlockCoord 2) : Measurable (fun ω => coarseBlockEntry (cubeSet Q) (X ω).toFun α β) := by
    by_cases h : α = β
    · simpa only [coarseBlockEntry,dite_eq_left h] using (hmu (blockBasis α)).const_mul 2
    · simp only [coarseBlockEntry,dite_eq_right h]
      convert ((hmu (blockBasis α+blockBasis β)).sub (hmu (blockBasis α))).sub
        (hmu (blockBasis β)) using 1
  apply measurable_pi_iff.mpr
  intro α
  apply measurable_pi_iff.mpr
  intro β
  cases α <;> cases β <;> simpa only [toFullBlockMat,coarseBlockMatrix] using he _ _


/-- Exact physical translation on every source cell. -/
theorem parent_boundary_band_coarse_cell_translate (M : ABKModel 2) (n J : ℤ)
    (weights : ℤ → ℝ) (Q : TriadicCube 2) (omega : Cutoff.CutoffSample 2) :
    coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M n J weights omega)=
      coarseBlockMatrix (cubeSet (originCube 2 Q.scale))
        (attenuatedCoefficient M n J weights (Cutoff.translateCutoffSample (triadicCubeShift Q) omega)) := by
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply congrArg (coarseBlockMatrix (cubeSet (originCube 2 Q.scale)))
  funext x
  exact (parent_boundary_band_translate M n J weights (triadicCubeShift Q) omega x).symm

/-- Exact signed-conjugation covariance of the actual finite-band matrix
on every origin square, with its variational witness proved internally. -/
theorem parent_boundary_band_coarse_sign_flip (M : ABKModel 2) (n J q : ℤ)
    (weights : ℤ → ℝ) (omega : Cutoff.CutoffSample 2) (i : Fin 2) :
    coarseBlockMatrix (openCubeSet (originCube 2 q))
      (attenuatedCoefficient M n J weights
        (Cutoff.rotateCutoffSample (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i) omega))=
      blockMatConj (signFlipMatrix i)
        (coarseBlockMatrix (openCubeSet (originCube 2 q)) (attenuatedCoefficient M n J weights omega)) := by
  have heq : attenuatedCoefficient M n J weights
      (Cutoff.rotateCutoffSample (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i) omega)=
      rotateCoeffField (signFlipMatrix i) (attenuatedCoefficient M n J weights omega) := by
    funext x
    exact parent_boundary_band_rotate M n J weights _ _ omega x
  rw [heq]
  exact coarseBlockMatrix_signFlip_openCubeSet_originCube_of_exists
    (parent_boundary_band_coarse_exists M n J weights omega (originCube 2 q)) i

/-- Exact coordinate-swap covariance on the same actual origin square. -/
theorem parent_boundary_band_coarse_swap (M : ABKModel 2) (n J q : ℤ)
    (weights : ℤ → ℝ) (omega : Cutoff.CutoffSample 2) (i j : Fin 2) :
    coarseBlockMatrix (openCubeSet (originCube 2 q))
      (attenuatedCoefficient M n J weights
        (Cutoff.rotateCutoffSample (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j) omega))=
      blockMatConj (Matrix.swap ℝ i j)
        (coarseBlockMatrix (openCubeSet (originCube 2 q)) (attenuatedCoefficient M n J weights omega)) := by
  have heq : attenuatedCoefficient M n J weights
      (Cutoff.rotateCutoffSample (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j) omega)=
      rotateCoeffField (Matrix.swap ℝ i j) (attenuatedCoefficient M n J weights omega) := by
    funext x
    exact parent_boundary_band_rotate M n J weights _ _ omega x
  rw [heq]
  exact coarseBlockMatrix_swap_openCubeSet_originCube_of_exists
    (parent_boundary_band_coarse_exists M n J weights omega (originCube 2 q)) i j

end
end ASDExplicitGamma.Native
