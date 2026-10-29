module

public import ASDExplicitGamma.Native.OldSignedPairedProjectionTrace

/-! Four-load ordinary projection gap with the favorable parent trace
kept exactly, for the weighted parent V budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- The four canonical quadratic forms give the actual coarse block trace. -/
theorem old_signed_coarse_basis_trace_sum (A : BlockMat 2) :
    (∑ c : BlockCoord 2,blockVecDot (blockBasis c) (blockMatVecMul A (blockBasis c)))=
      Matrix.trace A.upperLeft+Matrix.trace A.lowerRight := by
  simp only [blockBasis_pairing,Fintype.sum_sum_type,blockMatEntry,Matrix.trace,Matrix.diag_apply]

/-- The complete four-load primal projection budget retains the negative
parent trace, without assuming that partial-law inverse trace is positive. -/
theorem old_signed_primal_projection_trace_gap (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    (∑ c : BlockCoord 2,oldSignedPrimalProjectionEnergy Q depth nu sigma hnu hsigma k (blockBasis c)) ≤
      lemmaVInverseDepthMax Q a depth *
        (descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1)-
          traceDefect (openCubeSet Q) a 1) := by
  intro a
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    old_signed_primal_projection_exact_bound Q depth nu sigma hnu hsigma k (blockBasis c))
  apply hh.trans_eq
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Homogenization.descendantsAverage_sum]
  simp_rw [old_signed_coarse_basis_trace_sum]
  dsimp only [a]
  simp only [traceDefect,inv_one,one_mul]
  rw [old_signed_descendants_average_sub,descendantsAverage_const]
  ring

end
end ASDExplicitGamma.Native
