module

public import ASDExplicitGamma.Scalar.OldHessianTrialBottomCovariancePairedBill
public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy
public import ASDExplicitGamma.Native.OldSignedRemainderCovarianceVector

/-! Original finite-parent covariance tangent, with its signed bulk intact. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The deterministic actual flat covariance root cap. -/
def oldHessianFlatCovarianceCap (Q : TriadicCube 2) (fine : ℕ) (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  |b| *Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)+
    (cubeScaleFactor Q/(3:ℝ)^fine)*planarC1*
      (Real.sqrt (mainFlatSigmaSq b L)*Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)+
        2*|b| *Real.sqrt (mainFlatSigmaSq b L))

theorem old_hessian_flat_covariance_cap_nonneg (Q : TriadicCube 2) (fine : ℕ) (b : ℝ) (L : {l : ℝ // 0<l}) :
    0≤oldHessianFlatCovarianceCap Q fine b L := by
  unfold oldHessianFlatCovarianceCap
  apply add_nonneg (mul_nonneg (abs_nonneg b) (Real.sqrt_nonneg _))
  apply mul_nonneg
  · exact mul_nonneg (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity)) (Real.sqrt_nonneg _)
  · positivity

/-- Exact constant-one contraction of the covariance remainder against
the same two actual bottom primal/reciprocal errors. -/
theorem old_hessian_flat_covariance_spatial (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    descendantsAverage Q fine (fun U => oldSignedCovarianceBeta Q U b L false*
      Real.sqrt (oldHessianBottomPairedCellEnergy Q U nu sigma hnu hsigma k))≤
    oldHessianFlatCovarianceCap Q fine b L*
      Real.sqrt (descendantsAverage Q fine (fun U => oldHessianBottomPairedCellEnergy Q U nu sigma hnu hsigma k)) := by
  have hb := old_signed_covariance_beta_bound Q fine b L false
  have he (U) : oldSignedCovarianceBeta Q U b L false^2=
      ∑ i : Fin 2,vectorPositiveHaarNorm U (oldSignedRemainderCovarianceField Q b L false i)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hroot : Real.sqrt (oldSignedCellAverage Q fine (fun U => oldSignedCovarianceBeta Q U.val b L false^2))≤
      oldHessianFlatCovarianceCap Q fine b L := by
    rw [old_signed_cell_average_eq_descendantsAverage Q fine (fun U => oldSignedCovarianceBeta Q U b L false^2)]
    simp_rw [he]
    exact hb
  rw [←old_signed_cell_average_eq_descendantsAverage Q fine (fun U => oldSignedCovarianceBeta Q U b L false*
      Real.sqrt (oldHessianBottomPairedCellEnergy Q U nu sigma hnu hsigma k)),
    ←old_signed_cell_average_eq_descendantsAverage Q fine (fun U => oldHessianBottomPairedCellEnergy Q U nu sigma hnu hsigma k)]
  have hh := old_signed_cell_average_cauchy Q fine (fun U => oldSignedCovarianceBeta Q U.val b L false)
    (fun U => Real.sqrt (oldHessianBottomPairedCellEnergy Q U.val nu sigma hnu hsigma k))
  have hs (U : OldSignedCellIndex Q fine) : (Real.sqrt (oldHessianBottomPairedCellEnergy Q U.val nu sigma hnu hsigma k))^2=
      oldHessianBottomPairedCellEnergy Q U.val nu sigma hnu hsigma k :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => vectorWeakHaarEnergy_nonneg U.val _))
  simp only [hs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))

end
end ASDExplicitGamma.Scalar
