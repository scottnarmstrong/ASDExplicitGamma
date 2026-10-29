module

public import ASDExplicitGamma.Cold.CoarseGramSign
public import ASDExplicitGamma.Cold.MatrixFrobeniusAlgebra

/-! # The actual unequal scalar blocks of the expected planar response -/

@[expose] public section
noncomputable section
open Homogenization Matrix
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The source centered expected response with its two potentially unequal blocks. -/
def coldGraphBlockMean (p q : ℝ) : FullBlockMat 2 :=
  toFullBlockMat (Book.Ch02.blockDiag (p • (1:Mat 2)) (q • (1:Mat 2)))

/-- Exact Frobenius bias of the source expected block form. -/
theorem coldGraphBlockMean_frobenius (p q : ℝ) :
    matrixFrobeniusSq (coldGraphBlockMean p q) = 2*(p^2+q^2) := by
  simp [matrixFrobeniusSq,coldGraphBlockMean,toFullBlockMat,Book.Ch02.blockDiag,
    Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  ring

/-- Exact ordinary trace, with physical dimension two. -/
theorem coldGraphBlockMean_trace (p q : ℝ) : (coldGraphBlockMean p q).trace = 2*(p+q) := by
  simp [Matrix.trace,coldGraphBlockMean,toFullBlockMat,Book.Ch02.blockDiag,
    Fintype.sum_sum_type,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  ring

/-- Exact expected cross term retaining both unequal block means. -/
theorem coldGraphBlockMean_inner (p q r s : ℝ) :
    matrixFrobeniusInner (coldGraphBlockMean p q) (coldGraphBlockMean r s) = 2*(p*r+q*s) := by
  simp [matrixFrobeniusInner,coldGraphBlockMean,toFullBlockMat,Book.Ch02.blockDiag,
    Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  ring

end ASDExplicitGamma.Cold
