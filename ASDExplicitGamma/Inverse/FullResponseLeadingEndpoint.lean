module

public import ASDExplicitGamma.Inverse.FullResponseProfileSigns
public import ASDExplicitGamma.Inverse.FullResponseLayerProfileEndpoint

/-! Source-preserving endpoint substitution for the three leading trace components. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The three literal rational-endpoint leading payments, before the source
Bt/KD/K0 affine combination is simplified. -/
def fullResponseLeadingEndpoint (γ D E C0 C1 M4 J W0 W1 : ℝ) (a : Fin 3) : ℝ :=
  let z := (3:ℝ)^(2*γ*D)
  let C := 3*(planarGradientCharge 40+1)
  ![E*((29/25:ℝ)+C*C0*(invFullM2:ℝ))*(invLayer (2*invGamma):ℝ)*J,
    E*(29/100:ℝ)*γ*z*(W0*(D*(invLayer (4*invGamma):ℝ)+(invLayerF (4*invGamma):ℝ))+
      W1*(invLayer (4*invGamma):ℝ)),
    E*C*C1*M4*γ*z*(W0*(D*(invL0:ℝ)+(invL1:ℝ))+W1*(invL0:ℝ))] a

/-- Exact source component substitution, including the corrected combined
L1plus/L0plus inequality. No false individual L1 bound is introduced. -/
theorem full_response_leading_endpoint_le (γ p D E C0 C1 M4 J W0 W1 : ℝ)
    (hγ : 0 ≤ γ) (hg : γ ≤ gammaZero) (hp : 0 ≤ p) (hD : 0 ≤ D)
    (hE : rootEdelta .full ≤ E) (hC0 : fullResponseTraceC0 ≤ C0)
    (hC1 : fullResponseTraceC1=C1)
    (hM4 : Real.sqrt (densityMomentBudget (rootQ .full) 4 1232) ≤ M4)
    (hJ : selectedJp γ p 377 ≤ J)
    (hW0 : physicalSelectedWaveBudget γ p 377 0 ≤ W0)
    (hW1 : physicalSelectedWaveBudget γ p 377 1 ≤ W1)
    (hcombined : W0*(invL1plus:ℝ)+W1*(invL0plus:ℝ) ≤ W0*(invL1:ℝ)+W1*(invL0:ℝ))
    (a : Fin 3) :
    fullResponseTraceLeadingBudget γ p D a ≤ fullResponseLeadingEndpoint γ D E C0 C1 M4 J W0 W1 a := by
  obtain ⟨hA0,hMass0,hFirst0,hJ0,hW00,hW10⟩ := full_response_profile_signs γ p hg hp
  have hEactual : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hE0 := hEactual.trans hE
  have hC0actual : 0 ≤ fullResponseTraceC0 := by unfold fullResponseTraceC0 rootTau; positivity
  have hC00 := hC0actual.trans hC0
  have hC10 : 0 ≤ C1 := by rw [← hC1]; unfold fullResponseTraceC1 rootTau; positivity
  have hM40 := (Real.sqrt_nonneg _).trans hM4
  have hJcap0 := hJ0.trans hJ
  have hW0cap0 := hW00.trans hW0
  have hW1cap0 := hW10.trans hW1
  have hS : 0 ≤ 3*(planarGradientCharge 40+1) := by unfold planarGradientCharge; positivity
  have hM20 : (0:ℝ) ≤ (invFullM2:ℝ) := by norm_num [invFullM2]
  have hA2 := bank_root_layer_sum_endpoint γ hγ hg
  have hA4 := full_response_wave_layer_endpoint γ hg
  have hA2cap0 := hA0.trans hA2
  have hA4cap0 := hMass0.trans hA4.1
  have hAfcap0 := hFirst0.trans hA4.2
  have hz : 0 ≤ (3:ℝ)^(2*γ*D) := by positivity
  have hL := full_response_positive_layer_endpoint_signs
  have hL00 := hL.1
  have hL10 := hL.2
  fin_cases a
  · have hB : fullResponseTraceBaseline ≤ (29/25:ℝ)+3*(planarGradientCharge 40+1)*C0*(invFullM2:ℝ) := by
      unfold fullResponseTraceBaseline
      rw [full_response_mean_endpoints.1]
      have hh := mul_le_mul_of_nonneg_left hC0 (mul_nonneg hS hM20)
      convert add_le_add (le_refl (29/25:ℝ)) hh using 1 <;> ring
    have hB0 := full_response_trace_baseline_nonneg.trans hB
    have hh1 := mul_le_mul hE hB full_response_trace_baseline_nonneg hE0
    have hh2 := mul_le_mul hh1 hA2 hA0 (mul_nonneg hE0 hB0)
    have hh3 := mul_le_mul hh2 hJ hJ0 (mul_nonneg (mul_nonneg hE0 hB0) hA2cap0)
    simpa [fullResponseTraceLeadingBudget,fullResponseLeadingEndpoint] using hh3
  · have hinner0 : 0 ≤ physicalSelectedWaveBudget γ p 377 0*
        (D*fullResponseWaveLayerMass γ+fullResponseWaveLayerFirst γ)+
          physicalSelectedWaveBudget γ p 377 1*fullResponseWaveLayerMass γ := by positivity
    have hvol := add_le_add (mul_le_mul_of_nonneg_left hA4.1 hD) hA4.2
    have hi := add_le_add
      (mul_le_mul hW0 hvol (by positivity) hW0cap0)
      (mul_le_mul hW1 hA4.1 hMass0 hW1cap0)
    have hk : 0 ≤ (29/25:ℝ)*γ*(3:ℝ)^(2*γ*D)/4 := by positivity
    have hc := mul_le_mul_of_nonneg_right hE hk
    have hh := mul_le_mul hc hi hinner0 (mul_nonneg hE0 hk)
    dsimp only [fullResponseTraceLeadingBudget,fullResponseLeadingEndpoint,fullResponseIdentityWaveBudget]
    simp only [Matrix.cons_val_succ',Matrix.cons_val_zero']
    convert! hh using 1 <;> ring
  · have hinner0 : 0 ≤ physicalSelectedWaveBudget γ p 377 0*(D*(invL0plus:ℝ)+(invL1plus:ℝ))+
        physicalSelectedWaveBudget γ p 377 1*(invL0plus:ℝ) := by positivity
    have hi := add_le_add
      (mul_le_mul_of_nonneg_right hW0 (add_nonneg (mul_nonneg hD hL.1) hL.2))
      (mul_le_mul_of_nonneg_right hW1 hL.1)
    have hL0 : (invL0plus:ℝ) ≤ (invL0:ℝ) := by exact_mod_cast invLayer_positive_caps.2.2.1.le
    have hlinear := mul_le_mul_of_nonneg_left hL0 (mul_nonneg hD hW0cap0)
    have hcomb : W0*(D*(invL0plus:ℝ)+(invL1plus:ℝ))+W1*(invL0plus:ℝ) ≤
        W0*(D*(invL0:ℝ)+(invL1:ℝ))+W1*(invL0:ℝ) := by
      calc
        _ = (D*W0)*(invL0plus:ℝ)+(W0*(invL1plus:ℝ)+W1*(invL0plus:ℝ)) := by ring
        _ ≤ (D*W0)*(invL0:ℝ)+(W0*(invL1:ℝ)+W1*(invL0:ℝ)) := add_le_add hlinear hcombined
        _ = _ := by ring
    have hinner := hi.trans hcomb
    have hc1 := mul_le_mul_of_nonneg_right hE hC10
    have hc2 := mul_le_mul hc1 hM4 (Real.sqrt_nonneg _) (mul_nonneg hE0 hC10)
    have hk : 0 ≤ γ*(3:ℝ)^(2*γ*D) := by positivity
    have hhalf : γ*(3:ℝ)^(2*γ*D)/2 ≤ γ*(3:ℝ)^(2*γ*D) := by linarith only [hk]
    have hc3 := mul_le_mul hc2 hhalf (by positivity) (mul_nonneg (mul_nonneg hE0 hC10) hM40)
    have hc4 := mul_le_mul_of_nonneg_left hc3 hS
    have hh := mul_le_mul hc4 hinner hinner0
      (mul_nonneg hS (mul_nonneg (mul_nonneg (mul_nonneg hE0 hC10) hM40) hk))
    dsimp only [fullResponseTraceLeadingBudget,fullResponseLeadingEndpoint,fullResponseActiveWaveBudget]
    simp only [Matrix.cons_val_succ',Matrix.cons_val_zero']
    rw [hC1]
    convert! hh using 1 <;> ring

end
end ASDExplicitGamma.Inverse
