module

public import ASDExplicitGamma.Model.Q3DerivativePointwise
public import ASDExplicitGamma.Triadic.PlanarDirectionSmooth
public import ASDExplicitGamma.Variational.LemmaVH2RemainderKernel

/-! The canonical covariance defect and its actual planar Sobolev witness. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Triadic
noncomputable section

 def q3CovarianceDefect (L : ℝ) (z x : Vec 2) : ℝ :=
  q3ProductCovariance (fun i => (x i-z i)/L)-1

 theorem q3CovarianceDefect_contDiff (L : ℝ) (z : Vec 2) : ContDiff ℝ 2 (q3CovarianceDefect L z) := by
  unfold q3CovarianceDefect q3ProductCovariance
  apply ContDiff.sub _ contDiff_const
  exact (q3Cov_contDiff_two.comp (by fun_prop)).mul (q3Cov_contDiff_two.comp (by fun_prop))

 def q3CovarianceDefectWitness (Q : TriadicCube 2) (L : ℝ) (z : Vec 2) : PlanarW2Infinity Q :=
  PlanarW2Infinity.ofContDiff Q (q3CovarianceDefect L z) (q3CovarianceDefect_contDiff L z)

 def q3CovarianceDefectGradient (L : ℝ) (z x : Vec 2) (i : Fin 2) : ℝ :=
  if i=0 then deriv q3Cov ((x 0-z 0)/L)*q3Cov ((x 1-z 1)/L)/L
  else q3Cov ((x 0-z 0)/L)*deriv q3Cov ((x 1-z 1)/L)/L

 def q3CovarianceDefectHessian (L : ℝ) (z x : Vec 2) (i j : Fin 2) : ℝ :=
  if i=0 then if j=0 then iteratedDeriv 2 q3Cov ((x 0-z 0)/L)*q3Cov ((x 1-z 1)/L)/L^2
    else deriv q3Cov ((x 0-z 0)/L)*deriv q3Cov ((x 1-z 1)/L)/L^2
  else if j=0 then deriv q3Cov ((x 0-z 0)/L)*deriv q3Cov ((x 1-z 1)/L)/L^2
    else q3Cov ((x 0-z 0)/L)*iteratedDeriv 2 q3Cov ((x 1-z 1)/L)/L^2

 theorem q3ScaledCoordinate_hasFDerivAt (L : ℝ) (z x : Vec 2) (i : Fin 2) :
    HasFDerivAt (fun y : Vec 2 => (y i-z i)/L) (L⁻¹ • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) x := by
  simpa only [div_eq_inv_mul] using! ((((ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)).hasFDerivAt.sub_const (z i)).const_mul L⁻¹)

 theorem q3Cov_scaled_hasFDerivAt (L : ℝ) (z x : Vec 2) (i : Fin 2) :
    HasFDerivAt (fun y : Vec 2 => q3Cov ((y i-z i)/L))
      (deriv q3Cov ((x i-z i)/L) • (L⁻¹ • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ))) x :=
  ((q3Cov_contDiff_two.differentiable (by norm_num)) _).hasDerivAt.comp_hasFDerivAt x
    (q3ScaledCoordinate_hasFDerivAt L z x i)

 theorem q3Cov_first_scaled_hasFDerivAt (L : ℝ) (z x : Vec 2) (i : Fin 2) :
    HasFDerivAt (fun y : Vec 2 => deriv q3Cov ((y i-z i)/L))
      (iteratedDeriv 2 q3Cov ((x i-z i)/L) • (L⁻¹ • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ))) x := by
  have hd : ContDiff ℝ 1 (deriv q3Cov) := q3Cov_contDiff_two.deriv'
  simpa only [show (2:ℕ)=1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, Function.comp_def] using!
    ((hd.differentiable (by norm_num)) _).hasDerivAt.comp_hasFDerivAt x (q3ScaledCoordinate_hasFDerivAt L z x i)

 theorem q3CovarianceDefect_smoothCoordinateDerivative (L : ℝ) (z x : Vec 2) (i : Fin 2) :
    smoothCoordinateDerivative (q3CovarianceDefect L z) i x = q3CovarianceDefectGradient L z x i := by
  have hd := ((q3Cov_scaled_hasFDerivAt L z x 0).mul (q3Cov_scaled_hasFDerivAt L z x 1)).sub_const 1
  change fderiv ℝ (fun y => q3Cov ((y 0-z 0)/L)*q3Cov ((y 1-z 1)/L)-1) x (basisVec i) = _
  have he := hd.fderiv
  simp only [Pi.mul_apply] at he
  rw [he]
  fin_cases i <;> simp [q3CovarianceDefectGradient, basisVec] <;> ring

 theorem q3CovarianceDefect_gradient_derivative (L : ℝ) (z x : Vec 2) (i j : Fin 2) :
    fderiv ℝ (q3CovarianceDefectGradient L z · i) x (basisVec j) = q3CovarianceDefectHessian L z x i j := by
  fin_cases i
  · have hd := ((q3Cov_first_scaled_hasFDerivAt L z x 0).mul (q3Cov_scaled_hasFDerivAt L z x 1)).mul_const L⁻¹
    change fderiv ℝ (fun y => deriv q3Cov ((y 0-z 0)/L)*q3Cov ((y 1-z 1)/L)/L) x (basisVec j) = _
    have he := hd.fderiv
    simp only [Pi.mul_apply, ← div_eq_mul_inv] at he
    rw [he]
    fin_cases j <;> simp [q3CovarianceDefectHessian, basisVec] <;> ring
  · have hd := ((q3Cov_scaled_hasFDerivAt L z x 0).mul (q3Cov_first_scaled_hasFDerivAt L z x 1)).mul_const L⁻¹
    change fderiv ℝ (fun y => q3Cov ((y 0-z 0)/L)*deriv q3Cov ((y 1-z 1)/L)/L) x (basisVec j) = _
    have he := hd.fderiv
    simp only [Pi.mul_apply, ← div_eq_mul_inv] at he
    rw [he]
    fin_cases j <;> simp [q3CovarianceDefectHessian, basisVec] <;> ring

 theorem q3CovarianceDefectWitness_gradient (Q : TriadicCube 2) (L : ℝ) (z x : Vec 2) :
    planarW1Value (q3CovarianceDefectWitness Q L z).gradient x = q3CovarianceDefectGradient L z x := by
  funext i
  exact q3CovarianceDefect_smoothCoordinateDerivative L z x i

 theorem q3CovarianceDefectWitness_hessian (Q : TriadicCube 2) (L : ℝ) (z x : Vec 2) :
    planarW1Derivative (q3CovarianceDefectWitness Q L z).gradient x = q3CovarianceDefectHessian L z x := by
  funext i j
  change fderiv ℝ (smoothCoordinateDerivative (q3CovarianceDefect L z) i) x (basisVec j) = _
  rw [show smoothCoordinateDerivative (q3CovarianceDefect L z) i = (q3CovarianceDefectGradient L z · i)
    from funext (fun x => q3CovarianceDefect_smoothCoordinateDerivative L z x i)]
  exact q3CovarianceDefect_gradient_derivative L z x i j

end
end ASDExplicitGamma.Variational
