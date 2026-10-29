module

public import ASDExplicitGamma.Inverse.AssemblyTraceSeries
public import ASDExplicitGamma.Inverse.BankRootProfileArithmetic
public import ASDExplicitGamma.Numerics.Enclosures

/-! Fixed numeric caps for the positive trace profile. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

theorem assembly_sensitivity_lt :
    rootAssemblySensitivity < (127/100:ℝ) := by
  unfold rootAssemblySensitivity
  have harg : (17444/10000:ℝ)*(1+resetAllOrderTau)*(10*waveGateEta .allOrder)
      ≤ 236/1000 := by
    norm_num [resetAllOrderTau,waveGateEta,Numerics.Wave.allOrderTau,
      Numerics.Wave.allOrderEta]
  have hpoly : Real.exp (236/1000:ℝ) < 127/100 := by
    have hTaylor : Real.exp (236/1000:ℝ) ≤ 1267/1000 :=
      ASDExplicitGamma.Numerics.exp_le_of_poly
        (q := (236/1000:ℝ)) (y := (1267/1000:ℝ)) (by norm_num)
        (n := 8) (by norm_num)
        (by norm_num [ASDExplicitGamma.Numerics.expPoly,
          ASDExplicitGamma.Numerics.expErr,Finset.sum_range_succ,Nat.factorial])
    exact lt_of_le_of_lt hTaylor (by norm_num)
  exact (Real.exp_le_exp.mpr harg).trans_lt hpoly

private theorem assembly_trace_density_moments_small :
    densityMomentBudget (allOrderDensity:ℝ) 2 1324 < 1/10^120 ∧
    densityMomentBudget (allOrderDensity:ℝ) 4 1324 < (23/10^61:ℝ)^2 := by
  norm_num [densityMomentBudget,rareMomentPolynomial,allOrderDensity]

private theorem assembly_sqrt_three_le_seven_fourths :
    Real.sqrt 3 ≤ (26/15:ℝ) := by
  apply Real.sqrt_le_iff.mpr
  constructor <;> norm_num

theorem assembly_trace_response_coefficient_bound :
    1+2*Real.sqrt 3*resetAllOrderTau < (2*10^16:ℝ) := by
  have hroot := assembly_sqrt_three_le_seven_fourths
  norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau] at hroot ⊢
  nlinarith [hroot]

private theorem assembly_gradient_charge_bound :
    planarGradientCharge 40+1 < (4*10^41:ℝ) := by
  norm_num [planarGradientCharge]

private theorem assembly_active_constant_lt_two :
    assemblyActiveConstant < 2 := by
  unfold assemblyActiveConstant waveGateEta
  norm_num [Numerics.Wave.allOrderEta,Numerics.Wave.allOrderTau]

theorem assembly_trace_sensitivity_caps :
    assemblyTraceBaseline < 3/2 ∧
    assemblyTraceWaveCoefficient < 1 := by
  have hM := assembly_trace_density_moments_small
  have hresp := assembly_trace_response_coefficient_bound
  have hcharge := assembly_gradient_charge_bound
  have hactive := assembly_active_constant_lt_two
  have hsens := assembly_sensitivity_lt
  have hτ0 : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hresp0 : 0 ≤ 1+2*Real.sqrt 3*resetAllOrderTau := by positivity
  have hcharge0 : 0 ≤ planarGradientCharge 40+1 := by
    norm_num [planarGradientCharge]
  have hactive0 : 0 ≤ assemblyActiveConstant := by
    unfold assemblyActiveConstant waveGateEta
    positivity
  have hq0 : 0 ≤ (allOrderDensity:ℝ) := by
    norm_num [allOrderDensity]
  have hM2 : 0 ≤ densityMomentBudget (allOrderDensity:ℝ) 2 1324 :=
    density_moment_budget_nonneg _ hq0 _ _ (by norm_num)
  have hM4 : 0 ≤ densityMomentBudget (allOrderDensity:ℝ) 4 1324 :=
    density_moment_budget_nonneg _ hq0 _ _ (by norm_num)
  have hbaseSmall :
      12*(1+2*Real.sqrt 3*resetAllOrderTau)*(planarGradientCharge 40+1)*
        assemblyActiveConstant*densityMomentBudget (allOrderDensity:ℝ) 2 1324
        < 1/1000 := by
    have h4 := hM2
    have hfactor :
        12*(1+2*Real.sqrt 3*resetAllOrderTau)*(planarGradientCharge 40+1)*
          assemblyActiveConstant ≤ 12*(2*10^16)*(4*10^41)*2 := by
      calc
        _ ≤ 12*(2*10^16)*(planarGradientCharge 40+1)*assemblyActiveConstant := by
          gcongr
        _ ≤ 12*(2*10^16)*(4*10^41)*assemblyActiveConstant := by
          gcongr
        _ ≤ 12*(2*10^16)*(4*10^41)*2 := by
          gcongr
    calc
      _ ≤ (12*(2*10^16)*(4*10^41)*2)*
          densityMomentBudget (allOrderDensity:ℝ) 2 1324 :=
        mul_le_mul_of_nonneg_right hfactor h4
      _ < 1/1000 := by nlinarith [hM.1]
  have hwaveSmall :
      12*(1+2*Real.sqrt 3*resetAllOrderTau)*(planarGradientCharge 40+1)*
        Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324) < 1/4 := by
    have hroot : Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324) ≤
        23/10^61 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · norm_num
      · exact hM.2.le
    calc
      _ ≤ 12*(2*10^16)*(4*10^41)*(23/10^61:ℝ) := by
        have hfactor :
            12*(1+2*Real.sqrt 3*resetAllOrderTau)*(planarGradientCharge 40+1) ≤
              12*(2*10^16)*(4*10^41) := by
          calc
            _ ≤ 12*(2*10^16)*(planarGradientCharge 40+1) := by gcongr
            _ ≤ 12*(2*10^16)*(4*10^41) := by gcongr
        calc
          _ = (12*(1+2*Real.sqrt 3*resetAllOrderTau)*
                (planarGradientCharge 40+1))*
                Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324) := by ring
          _ ≤ (12*(2*10^16)*(4*10^41))*
                Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324) :=
              mul_le_mul_of_nonneg_right hfactor (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hroot (by positivity)
      _ < 1/4 := by norm_num
  constructor
  · calc
      assemblyTraceBaseline = rootAssemblySensitivity *
          ((29/25:ℝ)+12*(1+2*Real.sqrt 3*resetAllOrderTau)*
            (planarGradientCharge 40+1)*assemblyActiveConstant*
            densityMomentBudget (allOrderDensity:ℝ) 2 1324) := rfl
      _ < (127/100)*((29/25:ℝ)+1/1000) := by
        have hbracket0 : 0 ≤ (29/25:ℝ)+12*(1+2*Real.sqrt 3*resetAllOrderTau)*
            (planarGradientCharge 40+1)*assemblyActiveConstant*
            densityMomentBudget (allOrderDensity:ℝ) 2 1324 := by positivity
        have hbracket : (29/25:ℝ)+12*(1+2*Real.sqrt 3*resetAllOrderTau)*
            (planarGradientCharge 40+1)*assemblyActiveConstant*
            densityMomentBudget (allOrderDensity:ℝ) 2 1324 ≤
            (29/25:ℝ)+1/1000 := by nlinarith [hbaseSmall]
        calc
          _ < (127/100)*((29/25:ℝ)+12*(1+2*Real.sqrt 3*resetAllOrderTau)*
              (planarGradientCharge 40+1)*assemblyActiveConstant*
              densityMomentBudget (allOrderDensity:ℝ) 2 1324) :=
            mul_lt_mul_of_pos_right hsens (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hbracket (by norm_num)
      _ < 3/2 := by norm_num
  · calc
      assemblyTraceWaveCoefficient = rootAssemblySensitivity *
          ((29/100:ℝ)+12*(1+2*Real.sqrt 3*resetAllOrderTau)*
            (planarGradientCharge 40+1)*
            Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324)) := rfl
      _ < (127/100)*((29/100:ℝ)+1/4) := by
        have hbracket0 : 0 ≤ (29/100:ℝ)+12*(1+2*Real.sqrt 3*resetAllOrderTau)*
            (planarGradientCharge 40+1)*
            Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324) := by positivity
        have hbracket : (29/100:ℝ)+12*(1+2*Real.sqrt 3*resetAllOrderTau)*
            (planarGradientCharge 40+1)*
            Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324) ≤
            (29/100:ℝ)+1/4 := by nlinarith [hwaveSmall]
        calc
          _ < (127/100)*((29/100:ℝ)+12*(1+2*Real.sqrt 3*resetAllOrderTau)*
              (planarGradientCharge 40+1)*
              Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324)) :=
            mul_lt_mul_of_pos_right hsens (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hbracket (by norm_num)
      _ < 1 := by norm_num

theorem assembly_root_layer_sum_cap (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ gammaZero) :
    rootLayerSum (2*γ) ≤ 101/100 := by
  have hγ' : γ ≤ 17/50000 := by simpa [gammaZero] using hγ
  have hLayer := bank_root_layer_sum_endpoint γ hγ0 hγ'
  have hcap := invLayer_caps.1
  have hcap' : invLayer (2*invGamma) < (101/100:ℚ) := by
    exact lt_trans hcap (by norm_num)
  have hcap'' : (invLayer (2*invGamma):ℝ) ≤ 101/100 := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hcap'.le
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at hcast
    exact hcast
  exact hLayer.trans hcap''

end
end ASDExplicitGamma.Inverse
