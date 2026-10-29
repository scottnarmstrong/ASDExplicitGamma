module

public import ASDExplicitGamma.Gaussian.DerivativeLaw
public import ASDExplicitGamma.Model.Q3DerivativeSmooth

/-! Actual first-derivative covariance in the frozen shell, with exact physical scaling. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Model
noncomputable section

private theorem q3_affine_hasDerivAt (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => q3Cov (a+b*s)) (deriv q3Cov (a+b*t)*b) t := by
  simpa only [Function.comp_def, id_eq, mul_one] using!
    ((q3Cov_contDiff_two.differentiable (by norm_num)) (a+b*t)).hasDerivAt.comp t
    (((hasDerivAt_id t).const_mul b).const_add a)

private theorem q3_deriv_affine_hasDerivAt (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => deriv q3Cov (a+b*s))
      (deriv (deriv q3Cov) (a+b*t)*b) t := by
  have hc : ContDiff ℝ (1+1) q3Cov := q3Cov_contDiff_two
  have hd : ContDiff ℝ 1 (deriv q3Cov) := hc.deriv'
  simpa only [Function.comp_def, id_eq, mul_one] using!
    ((hd.differentiable (by norm_num)) (a+b*t)).hasDerivAt.comp t
    (((hasDerivAt_id t).const_mul b).const_add a)

private theorem q3_product_line_deriv (A c : ℝ) (x y v : Vec 2) :
    deriv (fun t : ℝ => A * q3Cov (c*(x 0-(y+t • v) 0)) *
      q3Cov (c*(x 1-(y+t • v) 1))) 0 =
      A * ((deriv q3Cov (c*(x 0-y 0))*(-c*v 0))*q3Cov (c*(x 1-y 1)) +
        q3Cov (c*(x 0-y 0))*(deriv q3Cov (c*(x 1-y 1))*(-c*v 1))) := by
  have h0 := q3_affine_hasDerivAt (c*(x 0-y 0)) (-c*v 0) 0
  have h1 := q3_affine_hasDerivAt (c*(x 1-y 1)) (-c*v 1) 0
  have heq (i : Fin 2) (t : ℝ) : c*(x i-(y+t • v) i) = c*(x i-y i)+(-c*v i)*t := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [heq]
  convert ((h0.const_mul A).mul h1).deriv using 1
  simp only [mul_zero, add_zero]
  ring

/-- The pointwise first-derivative covariance, before restoring the shell scale.
The tensor trace and directional Lipschitz constant have different payments. -/
theorem supMean_q3_first_covariance_diagonal (A c : ℝ) (x v w : Vec 2) :
    shellObservationApply (.first x v) (fun a =>
      shellObservationApply (.first x w) (fun b =>
        A*q3Cov (c*(a 0-b 0))*q3Cov (c*(a 1-b 1)))) =
      A*c^2*(78/5:ℝ)*(v 0*w 0+v 1*w 1) := by
  simp only [shellObservationApply, q3_product_line_deriv]
  have h0 := q3_affine_hasDerivAt 0 (c*v 0) 0
  have h1 := q3_affine_hasDerivAt 0 (c*v 1) 0
  have hd0 := q3_deriv_affine_hasDerivAt 0 (c*v 0) 0
  have hd1 := q3_deriv_affine_hasDerivAt 0 (c*v 1) 0
  have heq (i : Fin 2) (t : ℝ) : c*((x+t • v) i-x i) = 0+(c*v i)*t := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [heq]
  have hh := (((hd0.mul_const (-c*w 0)).mul h1).add
    (h0.mul (hd1.mul_const (-c*w 1)))).const_mul A
  simp only [Pi.mul_apply, Pi.add_apply] at hh
  rw [hh.deriv]
  have hd : deriv q3Cov 0 = 0 := by
    simpa only [iteratedDeriv_one] using q3Cov_odd_derivatives_zero.1
  have hdd : deriv (deriv q3Cov) 0 = -(78/5:ℝ) := by
    simpa only [show (2:ℕ)=1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      q3Cov_iteratedDeriv_values.1
  simp only [mul_zero, add_zero, hd, hdd, q3Cov_at_zero]
  ring

/-- The actual stored shell derivatives have this physical covariance, in every
integer shell, for arbitrary directions and repeated observation points. -/
theorem supMean_shell_first_covariance_diagonal (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x v w : Vec 2) :
    (∫ j, shellDerivativeEval (.first x v) j * shellDerivativeEval (.first x w) j
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
        (h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))*((3:ℝ)^k)⁻¹^2*(78/5:ℝ)*
          (v 0*w 0+v 1*w 1) := by
  rw [q3Shell_stored_derivative_covariance M h hM]
  exact supMean_q3_first_covariance_diagonal _ _ x v w

end
end ASDExplicitGamma.Gaussian
