module

public import ASDExplicitGamma.Scalar.OldHessianTrialTenTerm
public import ASDExplicitGamma.Main.Q3HeatIdentity
public import ASDExplicitGamma.Main.AffineMatrixSymmetry

/-! Unit-direction inverse response `e . D e` of the OLD parent response and its
heat derivative along the actual q3 directions. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Set
noncomputable section

/-- The observable `F_e(a) = e . D_Q(a/sigma) e` on compact coefficients. -/
def oldHessianUnitObservable (n : ℤ) (nu sigma : ℝ) (e : Vec 2) :
    C(closure (cubeSet (originCube 2 n)),ℝ) → ℝ := fun x =>
  sigma*vecDot e (matVecMul (coarseBlockMatrix (cubeSet (originCube 2 n))
    (responsePlanarCoefficientField nu
      (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ x))).lowerRight e)

theorem old_hessian_unit_observable_eq_energy (n : ℤ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (e : Vec 2) (x : C(closure (cubeSet (originCube 2 n)),ℝ)) :
    oldHessianUnitObservable n nu sigma e x =
      responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 n))
        (volume_cubeSet_toReal_pos (originCube 2 n)) nu sigma hnu hsigma (0,e)
        (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ x) := by
  rw [responseFrameEnergyObservable_eq_frameCoarseQuadratic]
  simp [oldHessianUnitObservable,frameMatrix,blockVecDot,blockMatVecMul,vecDot,matVecMul,
    Fin.sum_univ_two,Finset.mul_sum]
  ring

theorem old_hessian_unit_observable_C2 (n : ℤ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (e : Vec 2) :
    HasPolynomiallyBoundedC2Derivatives (oldHessianUnitObservable n nu sigma e) := by
  have hE := responseFrameEnergyObservable_hasPolynomiallyBoundedC2Derivatives
    (measurableSet_cubeSet (originCube 2 n)) (volume_cubeSet_toReal_pos (originCube 2 n))
    nu sigma hnu hsigma (0,e)
  have hc := hasPolynomiallyBoundedC2Derivatives_comp_isometry
    (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 n))) ℝ ℝ).toLinearIsometry hE
  have hfun : oldHessianUnitObservable n nu sigma e = fun x =>
      responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 n))
        (volume_cubeSet_toReal_pos (originCube 2 n)) nu sigma hnu hsigma (0,e)
        ((ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 n))) ℝ ℝ).toLinearIsometry x) :=
    funext (fun x => old_hessian_unit_observable_eq_energy n nu sigma hnu hsigma e x)
  rw [hfun]
  exact hc

/-- Heat derivative at `t=0` of any polynomially controlled C2 observable, along the
actual q3 directions. -/
theorem old_hessian_heat_deriv (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n m : ℤ)
    (Φ : C(closure (cubeSet (originCube 2 n)),ℝ) → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    HasDerivWithinAt (modelHeatAverage (closure (cubeSet (originCube 2 n))) M m Φ)
      ((1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 n))) M m Φ
        (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (m+1)) (q3ModelLength (m+1))) 0)
      (Ici 0) 0 := by
  let b := q3ModelAmplitude M h (m+1)
  let L := q3ModelLength (m+1)
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hA := mainCubeQ3Directions_summable n b L
  have hlaw := main_actual_fresh_cube_factor_law n M h hM m
  have hh := @main_c1On_modelHeatAverage_of_realization (MainCubeH3 n b L)
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance inferInstance inferInstance
    K inferInstance M ell m hK (mainCubeQ3Directions n b L) hA (mainCubeH3Value n b L) hlaw Φ hΦ
  exact hh.2.2.2

end
end ASDExplicitGamma.Scalar
