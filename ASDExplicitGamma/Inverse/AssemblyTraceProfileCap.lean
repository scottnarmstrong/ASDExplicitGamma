module

public import ASDExplicitGamma.Inverse.AssemblyTraceSeries
public import ASDExplicitGamma.Inverse.AssemblyTraceProfile
public import ASDExplicitGamma.Inverse.AssemblyTraceWaveProfile
public import ASDExplicitGamma.Inverse.AssemblyTraceMatrixProfile
public import ASDExplicitGamma.Inverse.AssemblyDensityProfile
public import ASDExplicitGamma.Inverse.AssemblyCorrelationProfile

/-! Numeric combination of the actual all-height trace budgets. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
noncomputable section

private theorem assembly_trace_density_factor_le_ten :
    assemblyTraceDensityFactor ≤ 10 := by
  have hτ0 : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hτ1 : 1 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num
  have hactive0 : 0 ≤ assemblyActiveConstant := by
    unfold assemblyActiveConstant waveGateEta
    positivity
  have hactive2 : assemblyActiveConstant ≤ 2 := by
    unfold assemblyActiveConstant waveGateEta
    norm_num [Numerics.Wave.allOrderEta,Numerics.Wave.allOrderTau]
  have hresponse0 : 0 < rootResponseEnvelope (6*resetAllOrderTau) := by
    unfold rootResponseEnvelope
    positivity
  have hresponse6 : 6*resetAllOrderTau ≤ rootResponseEnvelope (6*resetAllOrderTau) := by
    unfold rootResponseEnvelope
    have hsqrt := Real.sqrt_nonneg ((6*resetAllOrderTau)*(6*resetAllOrderTau+2))
    linarith
  have hsqrtτ : 2*Real.sqrt 3*resetAllOrderTau ≤ 4*resetAllOrderTau := by
    have hmul := mul_le_mul_of_nonneg_right hsqrt hτ0
    nlinarith
  have hlinear : 1+2*Real.sqrt 3*resetAllOrderTau ≤ 1+4*resetAllOrderTau := by
    linarith
  have hnum : 4*(1+2*Real.sqrt 3*resetAllOrderTau)*assemblyActiveConstant ≤
      40*resetAllOrderTau := by
    calc
      _ ≤ 4*((1+4*resetAllOrderTau)*assemblyActiveConstant) := by
        calc
          _ = 4*((1+2*Real.sqrt 3*resetAllOrderTau)*assemblyActiveConstant) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlinear hactive0) (by norm_num)
      _ ≤ 4*((1+4*resetAllOrderTau)*2) := by
        have hscaled := mul_le_mul_of_nonneg_left hactive2
          (show 0 ≤ 1+4*resetAllOrderTau by linarith)
        calc
          _ = 4*((1+4*resetAllOrderTau)*assemblyActiveConstant) := by ring
          _ ≤ 4*((1+4*resetAllOrderTau)*2) :=
            mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ ≤ 40*resetAllOrderTau := by nlinarith [hτ1]
  unfold assemblyTraceDensityFactor
  apply (div_le_iff₀ hresponse0).2
  nlinarith [hnum,hresponse6,hτ0]

private theorem assembly_density_budget_nonneg
    (γ : ℝ) (hγ : γ ≤ gammaZero) (k H0 : ℕ) :
    0 ≤ assemblyDensityBudget γ k H0 := by
  rw [← (assembly_density_budget_hasSum γ hγ k H0).tsum_eq]
  apply tsum_nonneg
  intro hk
  exact assembly_density_budget_term_nonneg γ k H0 hk

private theorem assembly_selected_clock_budget_nonneg
    (γ p : ℝ) (H0 : ℕ) (_hγ0 : 0 ≤ γ) :
    0 ≤ assemblySelectedClockBudget γ p H0 := by
  have htail : 0 ≤ selectedWaveExactTail (γ/2) (p/2) H0 0 := by
    unfold selectedWaveExactTail
    apply tsum_nonneg
    intro n
    simp only [Fin.val_zero, pow_zero]
    unfold selectedTailProbability
    positivity
  unfold assemblySelectedClockBudget
  positivity

private theorem assembly_trace_baseline_nonneg :
    0 ≤ assemblyTraceBaseline := by
  have hτ : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hq : 0 ≤ (allOrderDensity:ℝ) := by
    norm_num [allOrderDensity]
  have hmoment := density_moment_budget_nonneg (allOrderDensity:ℝ)
    hq 2 1324 (by norm_num)
  have hsens := root_assembly_sensitivity_pos.le
  unfold assemblyTraceBaseline assemblyActiveConstant
    planarGradientCharge waveGateEta
  positivity

private theorem assembly_root_layer_sum_nonneg (γ : ℝ) :
    0 ≤ rootLayerSum (2*γ) := by
  unfold rootLayerSum
  apply tsum_nonneg
  intro i
  exact mul_nonneg (bankLayerWeight_nonneg i) (by positivity)

/-- The actual selected-clock, direct whole-root wave, reset-matrix, D2
density, and two D4 common-noise budgets fit the source trace profile. -/
theorem assembly_trace_profile_budget_cap
    (γ p D : ℝ) (hγ : γ ≤ gammaZero) (hγ0 : 0 ≤ γ)
    (hp : 2 ≤ p) (hD : 0 ≤ D) :
    let k := orderBand p
    let E := heightEntrance k
    assemblyTraceSeriesSelectedBudget γ p D k ≤
      (2+2810*γ*((E:ℝ)+20+p*(D+1)))*
        (3:ℝ)^(4*γ*((E:ℝ)+20)+2*γ*D) := by
  let k := orderBand p
  let E := heightEntrance k
  let H0 := E+5
  let A := (E:ℝ)+20+p*(D+1)
  let T := (3:ℝ)^(4*γ*((E:ℝ)+20))
  let X := (3:ℝ)^(2*γ*D)
  let R := (3:ℝ)^(4*γ*((E:ℝ)+20)+2*γ*D)
  dsimp only
  rw [assemblyTraceSeriesSelectedBudget]
  have hE : 333 ≤ E := by dsimp [E]; unfold heightEntrance; omega
  have hEreal : (333:ℝ) ≤ E := by exact_mod_cast hE
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hγA : 0 ≤ γ*A := mul_nonneg hγ0 hA0
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hTleR : T ≤ R := by
    dsimp [T,R]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    nlinarith [hγ0,hD]
  have hXleR : X ≤ R := by
    dsimp [X,R]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    have hentrance : 0 ≤ (E:ℝ)+20 := by linarith
    nlinarith [hγ0,hentrance]
  have hRone : 1 ≤ R := by
    dsimp [R]
    apply Real.one_le_rpow (by norm_num : (1:ℝ)≤3)
    have hentrance : 0 ≤ (E:ℝ)+20 := by linarith
    positivity
  have hbaseCap := (assembly_trace_sensitivity_caps).1.le
  have hlayerCap := assembly_root_layer_sum_cap γ hγ0 hγ
  have hclockCap : assemblySelectedClockBudget γ p E ≤ (1001/1000:ℝ)*T := by
    simpa only [T] using
      (assembly_selected_clock_normed_cap γ p hγ hγ0 hp)
  have hwaveCap :
      assemblyWholeRootWaveSelectedSeriesBudget γ p D E ≤
        2600*γ*A*R := by
    simpa only [A,R] using
      (assembly_selected_wave_series_normed_cap γ p D hγ hγ0 hp hD)
  have hmatrixCap :
      assemblyTraceMatrixBudget γ p D (E+5) ≤
        1/100+γ*A*X := by
    simpa only [A,X] using
      (assembly_trace_matrix_profile_cap γ p D hγ hγ0 hp hD)
  have hdensityCap :
      assemblyDensityBudget γ k (E+5) ≤ 1/100 := by
    simpa only [k] using assembly_trace_density_profile_cap γ p hγ hp
  have hcorrCap :
      assemblyTraceCorrelationCoefficient*γ*X*
        (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0+
          40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1) ≤
        200*γ*A*X := by
    simpa only [A,X] using
      (assembly_trace_correlation_profile_cap γ p D hγ hγ0 hp hD)
  have hbaseline0 : 0 ≤ assemblyTraceBaseline :=
    assembly_trace_baseline_nonneg
  have hlayer0 : 0 ≤ rootLayerSum (2*γ) :=
    assembly_root_layer_sum_nonneg γ
  have hclock0 : 0 ≤ assemblySelectedClockBudget γ p E :=
    assembly_selected_clock_budget_nonneg γ p E hγ0
  have hbaselineClock :
      assemblyTraceBaseline*rootLayerSum (2*γ)*
        assemblySelectedClockBudget γ p E ≤ (8/5:ℝ)*R := by
    have hfirst : assemblyTraceBaseline*rootLayerSum (2*γ) ≤
        (3/2:ℝ)*(101/100:ℝ) :=
      mul_le_mul hbaseCap hlayerCap hlayer0 (by norm_num)
    calc
      _ ≤ ((3/2:ℝ)*(101/100:ℝ))*
          assemblySelectedClockBudget γ p E :=
        mul_le_mul_of_nonneg_right hfirst hclock0
      _ ≤ ((3/2:ℝ)*(101/100:ℝ))*((1001/1000:ℝ)*T) :=
        mul_le_mul_of_nonneg_left hclockCap (by norm_num)
      _ = ((3/2:ℝ)*(101/100:ℝ)*(1001/1000))*T := by ring
      _ ≤ (8/5:ℝ)*T :=
        mul_le_mul_of_nonneg_right (by norm_num) hT0
      _ ≤ (8/5:ℝ)*R :=
        mul_le_mul_of_nonneg_left hTleR (by norm_num)
  have hwave0 :
      0 ≤ assemblyWholeRootWaveSelectedSeriesBudget γ p D E :=
    assembly_whole_root_wave_selected_series_budget_nonneg
      γ p D hγ hγ0 hp E hE hD
  have hwave :
      assemblyTraceWaveCoefficient*
        assemblyWholeRootWaveSelectedSeriesBudget γ p D E ≤
          2600*γ*A*R := by
    calc
      _ ≤ 1*assemblyWholeRootWaveSelectedSeriesBudget γ p D E :=
        mul_le_mul_of_nonneg_right
          (assembly_trace_sensitivity_caps).2.le hwave0
      _ = assemblyWholeRootWaveSelectedSeriesBudget γ p D E := by ring
      _ ≤ 2600*γ*A*R := hwaveCap
  have hdensity0 : 0 ≤ assemblyDensityBudget γ k (E+5) :=
    assembly_density_budget_nonneg γ hγ k (E+5)
  have hdensity :
      assemblyTraceDensityFactor*assemblyDensityBudget γ k (E+5) ≤
        (1/10:ℝ)*R := by
    have hsmall :
        assemblyTraceDensityFactor*assemblyDensityBudget γ k (E+5) ≤
          1/10 := by
      calc
        _ ≤ 10*(1/100:ℝ) :=
          mul_le_mul assembly_trace_density_factor_le_ten hdensityCap
            hdensity0 (by norm_num)
        _ = 1/10 := by norm_num
    calc
      _ ≤ (1/10:ℝ) := hsmall
      _ = (1/10)*1 := by ring
      _ ≤ (1/10)*R := mul_le_mul_of_nonneg_left hRone (by norm_num)
  have hmatrix :
      assemblyTraceMatrixBudget γ p D (E+5) ≤
        (1/100:ℝ)*R+γ*A*R := by
    calc
      _ ≤ (1/100:ℝ)+γ*A*X := hmatrixCap
      _ ≤ (1/100:ℝ)*R+γ*A*R := by
        exact add_le_add
          (by
            calc
              (1/100:ℝ) = (1/100)*1 := by ring
              _ ≤ (1/100)*R :=
                mul_le_mul_of_nonneg_left hRone (by norm_num))
          (mul_le_mul_of_nonneg_left hXleR hγA)
  have hcorr :
      assemblyTraceCorrelationCoefficient*γ*X*
        (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0+
          40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1) ≤
        200*γ*A*R := by
    calc
      _ ≤ 200*γ*A*X := hcorrCap
      _ ≤ 200*γ*A*R := mul_le_mul_of_nonneg_left hXleR
        (by positivity)
  have hsum1 :
      assemblyTraceBaseline*rootLayerSum (2*γ)*
          assemblySelectedClockBudget γ p E+
        assemblyTraceWaveCoefficient*
          assemblyWholeRootWaveSelectedSeriesBudget γ p D E ≤
      (8/5:ℝ)*R+2600*γ*A*R := by exact add_le_add hbaselineClock hwave
  have hsum2 :
      assemblyTraceBaseline*rootLayerSum (2*γ)*
          assemblySelectedClockBudget γ p E+
        assemblyTraceWaveCoefficient*
          assemblyWholeRootWaveSelectedSeriesBudget γ p D E+
        assemblyTraceMatrixBudget γ p D (E+5) ≤
      (8/5:ℝ)*R+2600*γ*A*R+((1/100:ℝ)*R+γ*A*R) :=
    by exact add_le_add hsum1 hmatrix
  have hsum3 :
      assemblyTraceBaseline*rootLayerSum (2*γ)*
          assemblySelectedClockBudget γ p E+
        assemblyTraceWaveCoefficient*
          assemblyWholeRootWaveSelectedSeriesBudget γ p D E+
        assemblyTraceMatrixBudget γ p D (E+5)+
        assemblyTraceDensityFactor*assemblyDensityBudget γ k (E+5) ≤
      (8/5:ℝ)*R+2600*γ*A*R+
        ((1/100:ℝ)*R+γ*A*R)+(1/10:ℝ)*R :=
    by exact add_le_add hsum2 hdensity
  have hsum :
      assemblyTraceBaseline*rootLayerSum (2*γ)*
          assemblySelectedClockBudget γ p E+
        assemblyTraceWaveCoefficient*
          assemblyWholeRootWaveSelectedSeriesBudget γ p D E+
        assemblyTraceMatrixBudget γ p D (E+5)+
        assemblyTraceDensityFactor*assemblyDensityBudget γ k (E+5)+
        assemblyTraceCorrelationCoefficient*γ*X*
          (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0+
            40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1) ≤
      (8/5:ℝ)*R+2600*γ*A*R+
        ((1/100:ℝ)*R+γ*A*R)+(1/10:ℝ)*R+200*γ*A*R :=
    by exact add_le_add hsum3 hcorr
  have hfinal :
      (8/5:ℝ)*R+2600*γ*A*R+
        ((1/100:ℝ)*R+γ*A*R)+(1/10:ℝ)*R+200*γ*A*R ≤
        (2+2810*γ*A)*R := by
    calc
      _ = (171/100:ℝ)*R+2801*(γ*A*R) := by ring
      _ ≤ 2*R+2810*(γ*A*R) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (by norm_num) hR0)
          (mul_le_mul_of_nonneg_right (by norm_num)
            (mul_nonneg hγA hR0))
      _ = (2+2810*γ*A)*R := by ring
  exact hsum.trans hfinal

end
end ASDExplicitGamma.Inverse
