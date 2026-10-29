module

public import ASDExplicitGamma.Native.OldSignedQ1OscillationCaps
public import ASDExplicitGamma.Native.OldSignedQ1ReciprocalContractions

/-! The complete reciprocal profile fits the frozen q1 endpoint fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- Both reciprocal loads retain the physical theta factor. -/
theorem old_signed_q1_scaled_reciprocal_profile
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (t : ℝ) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    let C := oldSignedQ1PanelHistory t
    let A := 1+2*C+Real.sqrt (2*C)
    let B := (3683/2500:ℝ)
    oldSignedQ1ReciprocalSpatialCap (originCube 2 n) 5 t b L ≤
      theta M*((B+1)^2*(nativeSetupQ1001FieldsR.getD 4 0)^2+
        B*A*(nativeSetupQ1001FieldsR.getD 5 0)^2) := by
  intro b L C A B
  let r := cubeScaleFactor (originCube 2 n)/3^5
  let S := nativeSetupQ1001FieldsR.getD 0 0*(1/531441)*(156/5)
  have hs : 0 ≤ S := mul_nonneg (mul_nonneg old_signed_q1_setup_variance_nonneg
    (by norm_num)) (by norm_num)
  have hA : 0 ≤ A := add_nonneg (add_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (sq_nonneg _))) (Real.sqrt_nonneg _)
  have hc : planarC0^2 ≤ (11/25:ℝ)^2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) old_signed_q1_planarC0_le 2
  have hg' : r^2*mainFlatSigmaSq b L ≤ theta M*S :=
    old_signed_q1_scaled_gradient_energy M h hg n hstate
  have hSigma : 0 ≤ mainFlatSigmaSq b L := by unfold mainFlatSigmaSq; positivity
  have hp := mul_le_mul hc hg' (mul_nonneg (sq_nonneg r) hSigma) (sq_nonneg (11/25:ℝ))
  have hf : 0 ≤ (B+1)^2*(1+Real.sqrt 2)^2+B*A :=
    add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (by norm_num [B]) hA)
  have hh := mul_le_mul_of_nonneg_right hp hf
  dsimp only [S] at hs
  simp only [old_signed_q1_setup_readable_04,old_signed_q1_setup_readable_05,
    mul_pow,Real.sq_sqrt hs]
  unfold oldSignedQ1ReciprocalSpatialCap
  convert hh using 1 <;> dsimp only [r,S,A,B,C] <;> ring

end
end ASDExplicitGamma.Native
