module

public import ASDExplicitGamma.Numerics.AllOrder.CirGates

/-! Source-domain versions of the CIR endpoint enclosures. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.AllOrder
open Mirror Scalar

noncomputable def cirA (rho : ℝ) : ℝ :=
  1.860+2.36412*rho*Real.sqrt (156/5)+0.52288*rho^2*Real.sqrt (46488/25)
noncomputable def cirB (rho : ℝ) : ℝ :=
  1.860+2.36412*rho*Real.sqrt (78/5)+0.52288*rho^2*Real.sqrt (23244/25)

theorem cir_radical_caps :
    Real.sqrt (156/5) < 5.586 ∧ Real.sqrt (46488/25) < 43.123 ∧
    Real.sqrt (78/5) < 3.950 ∧ Real.sqrt (23244/25) < 30.493 ∧
    Real.sqrt 2.265 < 1.506 ∧ (3.46 : ℝ) < Real.sqrt 12 ∧
    (3 : ℝ)^(16/327680 : ℝ) < 1001/1000 := by
  obtain ⟨h1,h2,h3,h4,h5,_,_,_,hp,_⟩ := cir_kernel_check
  have hh1 := scalar_upper_sound _ _ h1
  have hh2 := scalar_upper_sound _ _ h2
  have hh3 := scalar_upper_sound _ _ h3
  have hh4 := scalar_upper_sound _ _ h4
  have hh5 := scalar_upper_sound _ _ h5
  have hhp := scalar_upper_sound _ _ hp
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · norm_num [sc,evalReal] at hh1 ⊢
    exact hh1
  · norm_num [sc,evalReal] at hh2 ⊢
    exact hh2
  · norm_num [sc,evalReal] at hh3 ⊢
    exact hh3
  · norm_num [sc,evalReal] at hh4 ⊢
    exact hh4
  · norm_num [sc,evalReal] at hh5 ⊢
    exact hh5
  · exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  · rw [Real.rpow_def_of_pos (by norm_num)]
    norm_num [sc,evalReal,cirPowerExpr,scalarRealEnv] at hhp ⊢
    simpa only [mul_comm] using hhp

/-- Geometric ratios are nonnegative, and the largest ratio gives the largest coefficients. -/
theorem cir_source_coefficients (rho : ℝ) (hr0 : 0 ≤ rho) (hr : rho ≤ 1/243) :
    cirA rho < 1.915 ∧ cirB rho < 1.899 ∧ (cirB rho)^2 < 4 ∧
    4*(cirB rho)^2 ≤ 16 := by
  have hr2 := pow_le_pow_left₀ hr0 hr 2
  have hA : cirA rho ≤ 1.860+(2.36412/243)*Real.sqrt (156/5)+
      (0.52288/243^2)*Real.sqrt (46488/25) := by
    unfold cirA
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2.36412)) (Real.sqrt_nonneg (156/5))
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (by norm_num : (0:ℝ) ≤ 0.52288)) (Real.sqrt_nonneg (46488/25))
    linarith only [h1,h2]
  have hB : cirB rho ≤ 1.860+(2.36412/243)*Real.sqrt (78/5)+
      (0.52288/243^2)*Real.sqrt (23244/25) := by
    unfold cirB
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2.36412)) (Real.sqrt_nonneg (78/5))
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (by norm_num : (0:ℝ) ≤ 0.52288)) (Real.sqrt_nonneg (23244/25))
    linarith only [h1,h2]
  have ha := hA.trans_lt cir_coefficient_caps.1
  have hb := hB.trans_lt cir_coefficient_caps.2.1
  have hb0 : 0 ≤ cirB rho := by unfold cirB; positivity
  have hsq : (cirB rho)^2 < 4 := by nlinarith only [hb,hb0]
  exact ⟨ha,hb,hsq,by linarith only [hsq]⟩

end ASDExplicitGamma.Numerics.AllOrder
