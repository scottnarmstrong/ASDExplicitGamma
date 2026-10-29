module

public import ASDExplicitGamma.Cold.HarmonicGraphMean
public import ASDExplicitGamma.Cold.ProjectedGraphEnergy
public import ASDExplicitGamma.Cold.MatrixFrobeniusAlgebra

/-! # Exact four-load graph normalization: twice the actual Frobenius defect -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The source factor two is an exact identity of actual matched primal/adjoint optimizers. -/
theorem square_matched_graph_identity (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a) :
    squareFourGraphEnergy Q v.primal v.adjoint =
      2*matrixFrobeniusSq (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)-1) := by
  unfold squareFourGraphEnergy
  simp_rw [harmonic_maximizer_graph_mean Q hEll _ _ _ (v.primal_max _),
    harmonic_maximizer_graph_mean Q (isEllipticFieldOn_adjointCoeffField hEll) _ _ _ (v.adjoint_max _),
    coarse_square_adjoint_block Q hEll]
  simp [matrixFrobeniusSq,toFullBlockMat,blockMatFlipFlux,blockVecDot,vecDot,matVecMul,
    Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.sub_apply,Matrix.one_apply,Pi.single_apply]
  ring

end ASDExplicitGamma.Cold
