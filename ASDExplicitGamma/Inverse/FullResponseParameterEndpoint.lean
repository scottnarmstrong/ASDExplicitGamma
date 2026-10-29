module

public import ASDExplicitGamma.Inverse.FullResponseLayerProfileEndpoint
public import ASDExplicitGamma.Numerics.Inverse.Full64
public import ASDExplicitGamma.Numerics.Inverse.Full128

/-! Genuine full-row sensitivity, active coefficients and rare-mean endpoints. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Gaussian
noncomputable section

/-- Literal full-row exponential sensitivity consumes the certified rational cap. -/
theorem full_response_Edelta_endpoint : rootEdelta .full ≤ (invFull128Ed:ℝ) := by
  let x : ℚ := (17444/10000)*(1+invFullTau)*(10/(80*(1+invFullTau)))
  have he : rootEdelta .full=Real.exp (x:ℝ) := by
    unfold rootEdelta
    norm_num [rootTau,rootWaveTuple,waveGateEta,Numerics.Wave.fullEta,
      Numerics.Wave.fullTau,invFullTau,x]
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by norm_num [x,invFullTau]
  have hx1 : (x:ℝ) < 1 := by norm_num [x,invFullTau]
  have hh := Real.exp_bound_div_one_sub_of_interval hx0 hx1
  have hi : (invFull128Ed:ℝ)=1/(1-(x:ℝ)) := by
    norm_num [invFull128Ed,invFull128Delta,invE,invFullTau,x]
  rwa [he,hi]

/-- The sharp actual constant coefficient fits the literal outward c0t. -/
theorem full_response_c0_endpoint : fullResponseTraceC0 ≤ (invFull128c0:ℝ) := by
  let δ := (invFull128Delta:ℝ)
  have hδ : 0 ≤ δ := by norm_num [δ,invFull128Delta,invFullTau]
  have hδeq : 10*waveGateEta .full=δ := by
    norm_num [δ,waveGateEta,Numerics.Wave.fullEta,Numerics.Wave.fullTau,invFull128Delta,invFullTau]
  have hs : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have hp := pow_le_pow_left₀ (show 0 ≤ 1+Real.sqrt 2*δ by positivity)
    (show 1+Real.sqrt 2*δ ≤ 1+2*δ by nlinarith only [mul_le_mul_of_nonneg_right hs hδ]) 2
  unfold fullResponseTraceC0
  rw [hδeq]
  calc
    _ ≤ 2*(1+2*δ)^2*(1+6*rootTau .full) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
        (by norm_num [rootTau])
    _ = _ := by norm_num [δ,rootTau,invFull128c0,invFull128Delta,invFullTau]

/-- The full-row wave coefficient agrees exactly with the literal c1t. -/
theorem full_response_c1_endpoint : fullResponseTraceC1=(invFull128c1:ℝ) := by
  norm_num [fullResponseTraceC1,rootTau,invFull128c1,invFullTau]

/-- Source rare means retain their exact full-row values. -/
theorem full_response_mean_endpoints :
    densityMomentBudget (rootQ .full) 2 1232=(invFullM2:ℝ) ∧
      densityMomentBudget (rootQ .full) 4 1232=(invFullM4:ℝ) := by
  simpa only [densityMomentBudget,rootQ] using full_moment_polynomials

/-- The literal outward full-row fourth-moment radical is sound. -/
theorem full_response_m4root_endpoint :
    Real.sqrt (densityMomentBudget (rootQ .full) 4 1232) ≤ (invFull128M4root:ℝ) := by
  rw [full_response_mean_endpoints.2]
  exact inv_sqrt_upper invFull128_radicals.1.le invFull128_radicals.2.1

/-- Full-row response envelope, before the source finite-order matrix prefactor. -/
theorem full_response_response_envelope_le :
    rootResponseEnvelope (rootTau .full) ≤ 2*rootTau .full+2 := by
  have hτ : 0 ≤ rootTau .full := by norm_num [rootTau]
  have hs : Real.sqrt (rootTau .full*(rootTau .full+2)) ≤ rootTau .full+1 :=
    (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith only [sq_nonneg (rootTau .full)]⟩
  unfold rootResponseEnvelope
  linarith only [hs]

/-- The actual matrix prefactor at p=64 fits its own source MC (sqrt64=8). -/
theorem full_response_matrix_prefactor64 :
    256*Real.sqrt 64*rootResponseEnvelope (rootTau .full) ≤ (invFull64MC:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left full_response_response_envelope_le
    (by norm_num : (0:ℝ) ≤ 256*Real.sqrt 64)
  have hs : Real.sqrt (64:ℝ)=8 := by
    apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0:ℝ)<8)).mpr
    norm_num
  rw [hs] at hh ⊢
  convert hh using 1
  norm_num [invFull64MC,rootTau,invFullTau]

/-- The distinct p=128 row uses the source sqrt128≤12 payment. -/
theorem full_response_matrix_prefactor128 :
    256*Real.sqrt 128*rootResponseEnvelope (rootTau .full) ≤ (invFull128MC:ℝ) := by
  have hs : Real.sqrt 128 ≤ 12 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have he0 : 0 ≤ rootResponseEnvelope (rootTau .full) := by
    unfold rootResponseEnvelope rootTau
    positivity
  have hh := mul_le_mul hs full_response_response_envelope_le he0 (by norm_num : (0:ℝ) ≤ 12)
  have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 256)
  convert hh' using 1 <;> norm_num [invFull128MC,rootTau,invFullTau]
  ring

end
end ASDExplicitGamma.Inverse
