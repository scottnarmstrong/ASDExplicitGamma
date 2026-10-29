module

public import ASDExplicitGamma.Variational.LemmaVAlgebra
public import Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.CoarseGaugeNullLagrangian

/-! The planar column-divergence cancellation, with a supplied zero-trace
residual. This module does not construct DIAG's interpolant. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

/-- A constant skew matrix applied to a zero-trace gradient is orthogonal
to every `H¹` gradient, with no boundary condition on the latter. -/
theorem lemmaVPlanar_rotatedGradient_zeroNormal {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpen U) (r : H10Function U) :
    IsSolenoidalZeroNormalTraceOn U
      (fun x => matVecMul responsePlanarJ (r.toH1Function.grad x)) := by
  intro w
  have hJ : matTranspose responsePlanarJ = -responsePlanarJ := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [matTranspose, responsePlanarJ]
  have h := isSolenoidalOn_matVecMul_of_isPotentialOn_of_transpose_eq_neg
    hU hJ w.isPotentialOn r
  have heq : (fun x => vecDot (matVecMul responsePlanarJ (r.toH1Function.grad x))
      (w.grad x)) = fun x =>
        -vecDot (matVecMul responsePlanarJ (w.grad x)) (r.toH1Function.grad x) := by
    funext x
    simp [vecDot, matVecMul, responsePlanarJ, Fin.sum_univ_two]
    ring
  rw [heq, integral_neg, h, neg_zero]

end

end ASDExplicitGamma.Variational
