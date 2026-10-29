module

public import ASDExplicitGamma.Native.GenericSourceShellBudget
public import ASDExplicitGamma.Numerics.Native.SetupQ1001Proof
public import ASDExplicitGamma.Numerics.Native.PanelNodes

/-! Exact physical q1 variance and its proportional frozen setup clock. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Inverse Numerics.Native Numerics.Mirror Algsuperdiff.Section3
noncomputable section

/-- Instructions only push values, so every pre-existing stack entry is retained. -/
theorem old_signed_plan_real_tail (stack : List ℝ) (ops : List Expr) (i : ℕ) :
    (nativePlanReal stack ops).getD (ops.length+i) 0=stack.getD i 0 := by
  induction ops generalizing stack i with
  | nil => simp only [nativePlanReal,List.length_nil,Nat.zero_add]
  | cons e es ih =>
    simp only [nativePlanReal,List.length_cons]
    rw [show es.length+1+i=es.length+(i+1) by omega,ih]
    rfl

private def variancePrefix : List Expr := [
  .const (2/1 : ℚ),
  .sqrt (.var 0),
  .const (3/1 : ℚ),
  .sqrt (.var 0),
  .sqrt (.var 0),
  .const (105/1 : ℚ),
  .sqrt (.var 0),
  .sqrt (.var 0),
  .sqrt (.var 0),
  .const (1/1 : ℚ),
  .divPos (.var 0) (.var 5),
  .add (.var 0) (.var 1),
  .const (3/20 : ℚ),
  .mul (.var 15) (.var 0),
  .exp (.var 0),
  .divPos (.var 5) (.var 0),
  .const (3/4 : ℚ),
  .mul (.var 19) (.var 0),
  .exp (.var 0),
  .const (17/25000 : ℚ),
  .mul (.var 22) (.var 0),
  .exp (.var 0),
  .const (153/100000 : ℚ),
  .mul (.var 1) (.var 0),
  .const (0/1 : ℚ),
  .add (.var 0) (.var 1)
]

/-- The setup variance is the true exponential shell clock, not its
larger rational generic-band replacement. -/
theorem old_signed_q1_setup_variance :
    nativeSetupQ1001FieldsR.getD 0 0=(9/2:ℝ)*gammaZero*(3:ℝ)^(2*gammaZero) := by
  have hsplit : nativeSetupQ1001Ops=variancePrefix++nativeSetupQ1001Ops.drop 26 := by decide +kernel
  have hlen : (nativeSetupQ1001Ops.drop 26).length=388 := by decide +kernel
  simp only [nativeSetupQ1001FieldsR,List.getD_cons_zero]
  rw [nativeSetupQ1001Real]
  rw [hsplit,nativePlanReal_append]
  have ht := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0) variancePrefix)
    (nativeSetupQ1001Ops.drop 26) 0
  simp only [hlen,Nat.add_zero] at ht
  rw [ht]
  simp only [variancePrefix,nativePlanReal,nativeSetupInputReal,evalReal,
    List.getD_cons_zero,List.getD_cons_succ]
  norm_num only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num only [gammaZero]
  ring

/-- The actual normalized one-shell variance fits the same exact setup
for every smaller gamma, with its full theta factor. -/
theorem old_signed_q1_model_variance
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    (q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ))^2≤
      theta M*(nativeSetupQ1001FieldsR.getD 0 0) := by
  have hv := native_source_shell_variance_le_clock M h n 1 1 hstate le_rfl
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2))
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (by norm_num : (0:ℝ)≤9/2) M.shellPrefix.gamma_pos.le)
  rw [div_pow]
  apply hv.trans
  simp only [nativeSourceShellClock,Nat.cast_one,mul_one] at hh ⊢
  rw [old_signed_q1_setup_variance]
  convert hh using 1
  unfold theta gammaZero
  ring

end
end ASDExplicitGamma.Native
