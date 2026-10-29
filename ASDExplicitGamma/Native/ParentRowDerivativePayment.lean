module

public import ASDExplicitGamma.Native.ParentRowWeightedFields
public import ASDExplicitGamma.Native.ParentBoundaryBandAffineBill
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Physical derivative variance paid by the exact mesh-five A2 field. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Algsuperdiff.Section3
noncomputable section

/-- Exact shell geometry identifies the derivative weight before the pi bound. -/
theorem parent_row_shell_derivative_clock (n : ℤ) (k : ℕ) (b : ℝ) :
    (cubeScaleFactor (originCube 2 n)/(Real.pi*(3:ℝ)^5))^2*
      mainFlatSigmaSq b (q3ModelLength (n+((k+1:ℕ):ℤ)))=
    (156/5:ℝ)/Real.pi^2*(b^2*(parentRowA2Weight k:ℝ)) := by
  have hr := parent_boundary_model_length_ratio n (k+1)
  have hgeom : (cubeScaleFactor (originCube 2 n))^2/
      (q3ModelLength (n+((k+1:ℕ):ℤ))).1^2=(1/9:ℝ)^(k+1) := by
    rw [←div_pow,hr,←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  calc
    _ = (156/5:ℝ)/Real.pi^2*b^2*
        ((cubeScaleFactor (originCube 2 n))^2/
          (q3ModelLength (n+((k+1:ℕ):ℤ))).1^2)*(1/9:ℝ)^5 := by
      unfold mainFlatSigmaSq
      field_simp
      ring
    _ = _ := by
      rw [hgeom]
      simp only [parentRowA2Weight,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
      rw [show k+6=(k+1)+5 by omega,pow_add]
      ring

/-- The complete physical derivative contribution fits the stored A2 coefficient. -/
theorem parent_row_actual_derivative_payment
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    (cubeScaleFactor (originCube 2 n)/(Real.pi*(3:ℝ)^5))^2*
      parentBoundaryBandDerivativeVariance M h n (j.val+1)≤
    theta M*((156/5:ℝ)*(parentRowFields j).getD 1 0/9) := by
  have hclock := parent_row_actual_a2_weighted_variance M h hg n hstate j
  have hcoef : (156/5:ℝ)/Real.pi^2≤(156/5:ℝ)/9 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith only [Real.pi_gt_three]
  unfold parentBoundaryBandDerivativeVariance
  rw [Finset.mul_sum]
  simp_rw [parent_row_shell_derivative_clock]
  rw [←Finset.mul_sum]
  have hsum : 0≤∑ i : Fin (j.val+1),
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2*
        (parentRowA2Weight i.val:ℝ) := by
    apply Finset.sum_nonneg
    intro i _
    unfold parentRowA2Weight
    positivity
  exact ((mul_le_mul_of_nonneg_right hcoef hsum).trans
    (mul_le_mul_of_nonneg_left hclock (by norm_num : (0:ℝ)≤(156/5)/9))).trans_eq (by ring)

end
end ASDExplicitGamma.Native
