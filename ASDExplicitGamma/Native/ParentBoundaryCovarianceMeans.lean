module

public import ASDExplicitGamma.Native.ParentBoundaryGramPairing

/-! Exact parent means of full flat covariance contractions. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

/-- Complete physical flat contraction has precisely its actual parent mean. -/
theorem parent_boundary_flat_mean_hasSum (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (i k : Fin 2) :
    HasSum (fun n : whiteBasisIndex => ∫ x,
      q3Convolution b L h3Zero (whiteBasis n) x *
        matVecMul responsePlanarJ (fun l => oldSignedFlatCoordinate Q b L plus n (i,l) x) k
          ∂normalizedCubeMeasure Q)
      (parentBoundaryFlatMean Q b L plus i k) := by
  have hs := old_signed_flat_covariance_integral Q b L plus i k (fun _ => 1) (memLp_const 1)
  simpa only [one_mul,integral_const,Measure.real_def,normalizedCubeMeasure_apply_univ,
    ENNReal.toReal_one,one_smul,mul_one,parentBoundaryFlatMean] using hs

/-- The first output coordinate of the minus contraction is a negative
actual mixed Dirichlet Gram mode, before any mode summation. -/
theorem parent_boundary_minus_covariance_mode_zero (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i : Fin 2) (n : whiteBasisIndex) :
    (∫ x,q3Convolution b L h3Zero (whiteBasis n) x *
      matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) 0
        ∂normalizedCubeMeasure Q) =
    -((cubeVolume Q)⁻¹ * inner ℝ
      (parentBoundaryDirichletLoadOperator Q b L (basisVec 1) (whiteBasis n))
      (parentBoundaryDirichletLoadOperator Q b L (mainFlatRotatedBasis i) (whiteBasis n))) := by
  have he : (fun x => q3Convolution b L h3Zero (whiteBasis n) x *
      matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) 0) =
      fun x => -(q3Convolution b L h3Zero (whiteBasis n) x *
        (lambda8Q3GaussianModeParentPotential Q b L (mainFlatRotatedBasis i) n).toH1Function.grad x 1) := by
    funext x
    simp [matVecMul,responsePlanarJ,Fin.sum_univ_two,old_signed_flat_minus_coordinate]
  rw [he,integral_neg,parent_boundary_gram_coordinate_integral]

/-- The second output coordinate is the other actual mixed Gram mode. -/
theorem parent_boundary_minus_covariance_mode_one (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i : Fin 2) (n : whiteBasisIndex) :
    (∫ x,q3Convolution b L h3Zero (whiteBasis n) x *
      matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) 1
        ∂normalizedCubeMeasure Q) =
    (cubeVolume Q)⁻¹ * inner ℝ
      (parentBoundaryDirichletLoadOperator Q b L (basisVec 0) (whiteBasis n))
      (parentBoundaryDirichletLoadOperator Q b L (mainFlatRotatedBasis i) (whiteBasis n)) := by
  have he : (fun x => q3Convolution b L h3Zero (whiteBasis n) x *
      matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) 1) =
      fun x => q3Convolution b L h3Zero (whiteBasis n) x *
        (lambda8Q3GaussianModeParentPotential Q b L (mainFlatRotatedBasis i) n).toH1Function.grad x 0 := by
    funext x
    simp [matVecMul,responsePlanarJ,Fin.sum_univ_two,old_signed_flat_minus_coordinate]
  rw [he,parent_boundary_gram_coordinate_integral]

/-- The full minus contraction has the exact scalar parent Gram mean.
No symmetry or mean identification is supplied as a premise. -/
theorem parent_boundary_minus_mean_scalar (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    parentBoundaryFlatMean (originCube 2 m) b L false i k =
      -parentBoundaryDirichletGram (originCube 2 m) b L 0 0 *
        (if k=i then 1 else 0) := by
  let Q := originCube 2 m
  have hg (j l : Fin 2) : HasSum (fun n : whiteBasisIndex =>
      (cubeVolume Q)⁻¹ * inner ℝ
        (parentBoundaryDirichletLoadOperator Q b L (basisVec j) (whiteBasis n))
        (parentBoundaryDirichletLoadOperator Q b L (basisVec l) (whiteBasis n)))
      (parentBoundaryDirichletGram Q b L j l) :=
    (parent_boundary_dirichlet_mixed_summable whiteBasis Q b L (basisVec j) (basisVec l)).hasSum.mul_left _
  have hs := parent_boundary_flat_mean_hasSum Q b L false i k
  fin_cases i <;> fin_cases k
  · have ht := (hg 1 1).neg.congr_fun (fun n => by
      exact (parent_boundary_minus_covariance_mode_zero Q b L 0 n).trans
        (by rw [old_signed_rotated_basis_zero]))
    have he := hs.unique ht
    simpa only [Q,←parent_boundary_dirichlet_gram_diagonal,ite_true,mul_one] using he
  · have ht := (hg 0 1).congr_fun (fun n => by
      exact (parent_boundary_minus_covariance_mode_one Q b L 0 n).trans
        (by rw [old_signed_rotated_basis_zero]))
    have he := hs.unique ht
    simpa [Q,parent_boundary_dirichlet_gram_offdiagonal] using he
  · have ht := (hg 1 0).congr_fun (fun n => by
      apply (parent_boundary_minus_covariance_mode_zero Q b L 1 n).trans
      rw [old_signed_rotated_basis_one,
        parent_boundary_dirichlet_load_neg,inner_neg_right,mul_neg,neg_neg])
    have he := hs.unique ht
    rw [parent_boundary_dirichlet_gram_symm] at he
    simpa [Q,parent_boundary_dirichlet_gram_offdiagonal] using he
  · have ht := (hg 0 0).neg.congr_fun (fun n => by
      apply (parent_boundary_minus_covariance_mode_one Q b L 1 n).trans
      rw [old_signed_rotated_basis_one,
        parent_boundary_dirichlet_load_neg,inner_neg_right,mul_neg])
    have he := hs.unique ht
    simpa only [Q,ite_true,mul_one] using he

end
end ASDExplicitGamma.Native
