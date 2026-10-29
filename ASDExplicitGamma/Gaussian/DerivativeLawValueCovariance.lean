module

public import ASDExplicitGamma.Gaussian.DerivativeLawQ3
public import ASDExplicitGamma.Gaussian.DerivativeLawCovarianceLimit

/-! Actual value covariances of the stored q3 shell at every integer level. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section

 theorem q3Kernel_nonnegative (x : ℝ) : 0 ≤ q3Kernel x := by
  unfold q3Kernel
  split_ifs with hx
  · have hsq := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at hsq
    exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by nlinarith only [hsq]) 3)
  · exact le_rfl

 theorem q3Cov_nonnegative (x : ℝ) : 0 ≤ q3Cov x :=
  integral_nonneg fun y => mul_nonneg (q3Kernel_nonnegative y) (q3Kernel_nonnegative (y+x))

 theorem q3ShellCovariance_nonnegative (M : ABKModel 2) (h : ℝ) (k : ℤ) (x y : Vec 2) :
    0 ≤ q3ShellCovariance M h k x y := by
  unfold q3ShellCovariance
  exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg h) (Real.rpow_nonneg (by norm_num) _)) (q3Cov_nonnegative _)) (q3Cov_nonnegative _)

 theorem q3ShellCovariance_diagonal (M : ABKModel 2) (h : ℝ) (k : ℤ) (x : Vec 2) :
    q3ShellCovariance M h k x x = h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)) := by
  simp only [q3ShellCovariance, sub_self, Pi.zero_apply, mul_zero, ASDExplicitGamma.Model.q3Cov_at_zero, mul_one]

 theorem q3ShellCovariance_symmetric (M : ABKModel 2) (h : ℝ) (k : ℤ) (x y : Vec 2) :
    q3ShellCovariance M h k y x = q3ShellCovariance M h k x y := by
  have he (i : Fin 2) : ((3:ℝ)^k)⁻¹*(y-x) i = -(((3:ℝ)^k)⁻¹*(x-y) i) := by simp only [Pi.sub_apply]; ring
  simp only [q3ShellCovariance, he, ASDExplicitGamma.Model.q3Cov_even]

 theorem q3Shell_value_sq_integral (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ) (x : Vec 2) :
    (∫ j, (shellScalarValue j x)^2 ∂(ShellField.shellMarginalLaw M.P k).toMeasure) = h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)) := by
  have hlaw := ASDExplicitGamma.Model.shellStream_linearCombination_law M h hM k 1 (fun _ => x) (fun _ => 1)
  have heq : ASDExplicitGamma.Model.shellStreamObservable 1 (fun _ => x) (fun _ => 1) = (fun j => shellScalarValue j x) := by
    funext j
    change (∑ i : Fin 1, (1:ℝ)*j x 1 0) = j x 1 0
    simp only [Fin.sum_univ_one, one_mul]
  rw [heq] at hlaw
  simp only [Fin.sum_univ_one, sub_self,
    Pi.zero_apply, mul_zero, ASDExplicitGamma.Model.q3Cov_at_zero, mul_one] at hlaw
  have hmeas : AEMeasurable (fun j => shellScalarValue j x) (ShellField.shellMarginalLaw M.P k).toMeasure := (shellDerivativeEval_continuous (.value x)).measurable.aemeasurable
  have h := integral_sq_of_map_gaussianReal_zero hmeas hlaw
  rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _))] at h
  exact h

/-- The frozen finite value law determines the actual (untruncated) scaled q3 covariance. -/
theorem q3Shell_value_covariance (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ) (x y : Vec 2) :
    (∫ j, shellScalarValue j x*shellScalarValue j y ∂(ShellField.shellMarginalLaw M.P k).toMeasure) = q3ShellCovariance M h k x y := by
  let A := h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  have hlaw := ASDExplicitGamma.Model.shellStream_linearCombination_law M h hM k 2 ![x,y] (fun _ => 1)
  have hv : h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))*(∑ i : Fin 2, ∑ j : Fin 2,
      (1:ℝ)*1*q3Cov (((3:ℝ)^k)⁻¹*(![x,y] i-![x,y] j) 0)*q3Cov (((3:ℝ)^k)⁻¹*(![x,y] i-![x,y] j) 1)) =
      2*A+2*q3ShellCovariance M h k x y := by
    calc
      _ = (q3ShellCovariance M h k x x+q3ShellCovariance M h k x y)+
          (q3ShellCovariance M h k y x+q3ShellCovariance M h k y y) := by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, q3ShellCovariance]
        ring
      _ = _ := by rw [q3ShellCovariance_diagonal, q3ShellCovariance_diagonal, q3ShellCovariance_symmetric]; dsimp [A]; ring
  rw [hv] at hlaw
  have hsumlaw : (ShellField.shellMarginalLaw M.P k).toMeasure.map (fun j => shellScalarValue j x+shellScalarValue j y) =
      gaussianReal 0 (Real.toNNReal (2*A+2*q3ShellCovariance M h k x y)) := by
    have heq : ASDExplicitGamma.Model.shellStreamObservable 2 ![x,y] (fun _ => 1) = (fun j => shellScalarValue j x+shellScalarValue j y) := by
      funext j
      change (∑ i : Fin 2, (1:ℝ)*j (![x,y] i) 1 0) = j x 1 0+j y 1 0
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    rw [← heq]
    exact hlaw
  have hmeas : AEMeasurable (fun j => shellScalarValue j x+shellScalarValue j y) (ShellField.shellMarginalLaw M.P k).toMeasure :=
    ((shellDerivativeEval_continuous (.value x)).measurable.aemeasurable).add ((shellDerivativeEval_continuous (.value y)).measurable.aemeasurable)
  have hsum := integral_sq_of_map_gaussianReal_zero hmeas hsumlaw
  rw [Real.coe_toNNReal _ (add_nonneg (mul_nonneg (by norm_num) hA) (mul_nonneg (by norm_num) (q3ShellCovariance_nonnegative M h k x y)))] at hsum
  have hg := q3Shell_values_gaussian M h hM k
  rw [integral_product_eq_polarization _ (hg.memLp x 2 (by simp)) (hg.memLp y 2 (by simp)),
    hsum, q3Shell_value_sq_integral M h hM k x, q3Shell_value_sq_integral M h hM k y]
  dsimp [A]
  ring

end
end ASDExplicitGamma.Gaussian
