module

public import ASDExplicitGamma.Scalar.OldHessianTrialJointMixedEnergy
public import ASDExplicitGamma.Scalar.OldHessianTrialCoarseWeakTrace

/-! The retained coarse product is aggregated over both bottom loads
before its original shifted OLD weak history is estimated. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Joint weak energy of the genuine cell-zero coarse potentials. -/
def oldHessianCoarseWeakBill (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) : ℝ :=
  oldSignedCellAverage Q coarse (fun D => ∑ i : Fin 2,vectorWeakHaarEnergy D.val
    (oldHessianCoarseCellPotential Q coarse nu sigma hnu hsigma k (basisVec i) D).toH1Function.grad)

/-- Exact common coarse mesh coefficient, including the full-column sqrt2. -/
def oldHessianCoarseColumnCoefficient (Q : TriadicCube 2) (coarse : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  Real.sqrt 2*((503/200:ℝ)*(cubeScaleFactor Q/(3:ℝ)^coarse/L.val)+
    (2031/500:ℝ)*(cubeScaleFactor Q/(3:ℝ)^coarse/L.val)^2)*|b|

/-- The sum of both literal column bills factors into the common physical
coarse coefficient and the joint cell-zero weak energy. -/
theorem old_hessian_coarse_column_joint_factor (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∑ i : Fin 2,oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k (basisVec i) b L)=
      oldHessianCoarseColumnCoefficient Q coarse b L^2*
        oldHessianCoarseWeakBill Q coarse nu sigma hnu hsigma k := by
  unfold oldHessianCoarseColumnBill
  rw [←old_signed_cell_average_sum]
  have he (D : OldSignedCellIndex Q coarse) : cubeScaleFactor D.val=cubeScaleFactor Q/(3:ℝ)^coarse :=
    cubeScaleFactor_descendant_eq_div_pow D.property
  simp_rw [he,←Finset.mul_sum]
  exact old_signed_cell_average_mul Q coarse _ _

/-- The actual shifted inverse-weighted trace on each coarse cell. -/
def oldHessianCoarseShiftedTrace (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (k : ResponseCoefficient (openCubeSet Q)) : ℝ :=
  oldSignedCellAverage Q coarse (fun D =>
    let kD := oldSignedCellCoefficient Q D.val (openCubeSet_subset_of_mem_descendantsAtDepth D.property) k
    let aD := responseFramePlanarCoefficientField nu sigma kD
    rawWeakTraceProxy (fun j => lemmaVInverseDepthMax D.val aD (1+j))
      (fun j => descendantsAverage D.val (1+j) (fun U => traceDefect (openCubeSet U) aD 1)))

/-- Root-zero cancellation of the genuine coarse potentials keeps alpha²
on the actual shifted trace, after summing both loads and all coarse cells. -/
theorem old_hessian_coarse_weak_shifted_trace (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    oldHessianCoarseWeakBill Q coarse nu sigma hnu hsigma k ≤
      inverseHistoryDiscount^2*oldHessianCoarseShiftedTrace Q coarse nu sigma k := by
  unfold oldHessianCoarseWeakBill oldHessianCoarseShiftedTrace
  rw [←old_signed_cell_average_mul]
  apply old_signed_cell_average_mono
  intro D
  exact old_hessian_coarse_cell_weak_trace Q D.val
    (openCubeSet_subset_of_mem_descendantsAtDepth D.property) nu sigma hnu hsigma k

end
end ASDExplicitGamma.Scalar
