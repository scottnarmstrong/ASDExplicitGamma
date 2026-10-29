module

public import ASDExplicitGamma.Native.OldSignedQ1PhysicalScales
public import ASDExplicitGamma.Main.FlatFieldH1Bounds
public import ASDExplicitGamma.Cold.NativeThetaScaling

/-! Physical amplitude and covariance roots against the exact q1 endpoint fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The full planar first derivative covariance has its exact 31.2 trace. -/
theorem old_signed_q1_sigma_eq (b : ℝ) (L : {l : ℝ // 0<l}) :
    mainFlatSigmaSq b L=(156/5)*b^2/L.val^2 := by
  unfold mainFlatSigmaSq
  ring

/-- A nonnegative spatial radius can be moved inside a covariance square root. -/
theorem old_signed_radius_sqrt (r x : ℝ) (hr : 0≤r) :
    r*Real.sqrt x=Real.sqrt (r^2*x) := by
  rw [Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr]

/-- The normalized physical amplitude has the exact square-root theta degree. -/
theorem old_signed_q1_scaled_amplitude
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    |q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)|≤
      Real.sqrt (theta M)*Real.sqrt (nativeSetupQ1001FieldsR.getD 0 0) := by
  calc
    _ = Real.sqrt ((q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ))^2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (theta M*(nativeSetupQ1001FieldsR.getD 0 0)) :=
      Real.sqrt_le_sqrt (old_signed_q1_model_variance M h hg n hstate)
    _ = _ := Real.sqrt_mul (cold_theta_pos M).le _

/-- The complete first covariance trace, with the actual cell radius,
fits the precise root used in the frozen oscillation and source fields. -/
theorem old_signed_q1_scaled_gradient_root
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    (cubeScaleFactor (originCube 2 n)/3^5)*Real.sqrt (mainFlatSigmaSq b L)≤
      Real.sqrt (theta M)*Real.sqrt (nativeSetupQ1001FieldsR.getD 0 0*(1/531441)*(156/5)) := by
  intro b L
  let r := cubeScaleFactor (originCube 2 n)/3^5
  have hr : 0≤r := div_nonneg (Triadic.cubeScaleFactor_pos' _).le (by positivity)
  have ha := old_signed_q1_model_second_moment M h hg n hstate
  rw [old_signed_q1_setup_readable_01] at ha
  have hh := mul_le_mul_of_nonneg_right ha (by norm_num : (0:ℝ)≤156/5)
  have hc : r^2*mainFlatSigmaSq b L≤
      theta M*(nativeSetupQ1001FieldsR.getD 0 0*(1/531441)*(156/5)) := by
    convert hh using 1
    · dsimp only [mainFlatSigmaSq,r,b,L]
      ring
    · ring
  rw [old_signed_radius_sqrt _ _ hr]
  exact (Real.sqrt_le_sqrt hc).trans_eq (Real.sqrt_mul (cold_theta_pos M).le _)

/-- The full Hessian covariance root retains its exact fourth mesh moment. -/
theorem old_signed_q1_scaled_hessian_root
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    (cubeScaleFactor (originCube 2 n)/3^5)^2*Real.sqrt ((46488/25)*b^2/L.val^4)≤
      Real.sqrt (theta M)*Real.sqrt (nativeSetupQ1001FieldsR.getD 0 0*(1/282429536481)*(46488/25)) := by
  intro b L
  let r := cubeScaleFactor (originCube 2 n)/3^5
  have hh := mul_le_mul_of_nonneg_right (old_signed_q1_model_variance M h hg n hstate)
    (by norm_num : (0:ℝ)≤(1/282429536481)*(46488/25))
  have he : (r^2)^2*((46488/25)*b^2/L.val^4)=b^2*((1/282429536481)*(46488/25)) := by
    have he4 := old_signed_q1_mesh_fourth n b
    calc
      _ = ((cubeScaleFactor (originCube 2 n)/3^5)^4*b^2/L.val^4)*(46488/25) := by dsimp only [r]; ring
      _ = _ := by rw [he4]; ring
  have hc : (r^2)^2*((46488/25)*b^2/L.val^4)≤
      theta M*(nativeSetupQ1001FieldsR.getD 0 0*(1/282429536481)*(46488/25)) := by
    rw [he]
    exact hh.trans_eq (by ring)
  rw [old_signed_radius_sqrt _ _ (sq_nonneg r)]
  exact (Real.sqrt_le_sqrt hc).trans_eq (Real.sqrt_mul (cold_theta_pos M).le _)

end
end ASDExplicitGamma.Native
