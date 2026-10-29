module

public import ASDExplicitGamma.Native.OldSignedFlatCoordinateIdentity

/-! Genuine source spaces of the existing OLD flat fields. Their boundary
conditions follow from their actual parent Dirichlet potentials. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- The existing plus coordinates are exactly a rotated Dirichlet residual. -/
theorem old_signed_flat_plus_rotated_residual (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    (fun x k => mainFlatPlusCoordinate Q b L n (i,k) x) = fun x =>
      matVecMul responsePlanarJ (q3Convolution b L h3Zero (whiteBasis n) x • basisVec i-
        (lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x) := by
  funext x k
  rw [old_signed_flat_plus_coordinate]
  simp only [sub_eq_add_neg,matVecMul_add,matVecMul_neg,matVecMul_smul,
    mainFlatRotatedBasis,Pi.add_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul]

/-- The actual plus flat mode is an H1 gradient, not merely a formal vector
field with finite energy. -/
theorem old_signed_flat_plus_potential (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    IsPotentialOn (openCubeSet Q) (fun x k => mainFlatPlusCoordinate Q b L n (i,k) x) := by
  rw [old_signed_flat_plus_rotated_residual]
  exact old_signed_rotated_solenoidal_potential Q
    ((old_signed_physical_raw_load_memL2 Q b L (whiteBasis n) i).sub
      (lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad_memVectorL2)
    (old_signed_q3_parent_residual_solenoidal Q b L (basisVec i) n)

/-- The correction from the unprojected plus load satisfies the actual
zero-normal trace on the parent boundary. -/
theorem old_signed_flat_plus_removed_zero_normal (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (fun x =>
      (fun k => mainFlatPlusCoordinate Q b L n (i,k) x)-
        q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i) := by
  have he : (fun x => (fun k => mainFlatPlusCoordinate Q b L n (i,k) x)-
        q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i) =
      (-1:ℝ) • (fun x => matVecMul responsePlanarJ
        ((lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x)) := by
    funext x k
    rw [Pi.sub_apply,old_signed_flat_plus_coordinate]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact isSolenoidalZeroNormalTraceOn_smul (planarJ_gradient_isSolenoidalZeroNormalTrace
    (lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n)) (-1)

/-- Actual minus coordinates are square integrable on the source square. -/
theorem old_signed_flat_minus_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    MemVectorL2 (openCubeSet Q) (fun x k => mainFlatMinusCoordinate Q b L n (i,k) x) := by
  apply MemLp.of_eval
  exact fun k => (mainFlatMinusCoordinate Q b L n (i,k)).memL2

/-- Actual plus coordinates are square integrable on the source square. -/
theorem old_signed_flat_plus_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    MemVectorL2 (openCubeSet Q) (fun x k => mainFlatPlusCoordinate Q b L n (i,k) x) := by
  apply MemLp.of_eval
  exact fun k => (mainFlatPlusCoordinate Q b L n (i,k)).memL2

end
end ASDExplicitGamma.Native
