module

public import ASDExplicitGamma.Inverse.FullResponseComponentConvergence

/-! Exact finite-order norm budgets of the actual source component series. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- Exact retained identity-wave budget. -/
def fullResponseIdentityWaveBudget (γ p D : ℝ) : ℝ :=
  (γ*(3:ℝ)^(2*γ*D)/4)*
    (physicalSelectedWaveBudget γ p 377 0*(D*fullResponseWaveLayerMass γ+fullResponseWaveLayerFirst γ)+
      physicalSelectedWaveBudget γ p 377 1*fullResponseWaveLayerMass γ)

/-- Exact corrected positive active-wave budget, before the combined K0 comparison. -/
def fullResponseActiveWaveBudget (γ p D : ℝ) : ℝ :=
  (γ*(3:ℝ)^(2*γ*D)/2)*
    (physicalSelectedWaveBudget γ p 377 0*(D*(Numerics.Inverse.invL0plus:ℝ)+(Numerics.Inverse.invL1plus:ℝ))+
      physicalSelectedWaveBudget γ p 377 1*(Numerics.Inverse.invL0plus:ℝ))

/-- Three source leading-series norm caps. -/
def fullResponseTraceLeadingBudget (γ p D : ℝ) (a : Fin 3) : ℝ :=
  ![(rootEdelta .full*fullResponseTraceBaseline*rootLayerSum (2*γ))*selectedJp γ p 377,
    (rootEdelta .full*(29/25:ℝ))*fullResponseIdentityWaveBudget γ p D,
    (rootEdelta .full*3*(planarGradientCharge 40+1)*fullResponseTraceC1*
      Real.sqrt (densityMomentBudget (rootQ .full) 4 1232))*fullResponseActiveWaveBudget γ p D] a

/-- Four source error-series norm caps, with density order p and wave order 2p. -/
def fullResponseTraceErrorBudget (γ p D : ℝ) (b : Fin 4) : ℝ :=
  let c := rootEdelta .full*fullResponseTraceC1*γ*(3:ℝ)^(2*γ*D)/2
  ![fullResponseTraceMatrixBudget γ p D 377,
    (rootEdelta .full*fullResponseTraceC0)*
      densityEZ γ (planarGradientCharge 40) (377-38),
    (c*D)*(40*(2*p+2)*densityD40 (rootQ .full) p 1232 γ (planarGradientCharge 40) (377-38)),
    c*(40*(2*p+2)*densityD41 (rootQ .full) p 1232 γ (planarGradientCharge 40) (377-38))] b

/-- The complete extended norm budget before rational endpoint comparisons. -/
def fullResponseTraceExtendedBudget (γ p D : ℝ) : ℝ≥0∞ :=
  (∑ a : Fin 3, ENNReal.ofReal (fullResponseTraceLeadingBudget γ p D a))+
    ∑ b : Fin 4, ENNReal.ofReal (fullResponseTraceErrorBudget γ p D b)

/-- Scalar multiplication of an actual complete series retains its exact norm cap. -/
theorem full_response_scaled_series_Lp {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) (f : I → Ω → ℝ) (c B : ℝ) (hc : 0 ≤ c)
    (hb : eLpNorm (fun ω => ∑' i, f i ω) p μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => ∑' i, c*f i ω) p μ ≤ ENNReal.ofReal (c*B) := by
  have he : (fun ω => ∑' i, c*f i ω)=c • (fun ω => ∑' i, f i ω) := by
    funext ω
    exact tsum_mul_left
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hc,ENNReal.ofReal_mul hc]
  exact mul_le_mul_of_nonneg_left hb bot_le

/-- Every actual selected leading component has its source norm budget. -/
theorem full_response_trace_leading_component_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (a : Fin 3) :
    eLpNorm (fun ω => ∑' k, fullResponseTraceLeading M Q N weights a k ω)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (fullResponseTraceLeadingBudget M.gamma p ((N:ℝ)-(Q.scale:ℝ)+1) a) := by
  fin_cases a
  · simpa [fullResponseTraceLeadingBudget] using
      full_response_baseline_series_Lp M h hM hg Q hpast N weights p hp hp256
  · have hh := full_response_identity_wave_series_Lp M h hM hg Q hpast N hN weights hw p hp hp256
    have hc : 0 ≤ rootEdelta .full*(29/25:ℝ) := by unfold rootEdelta; positivity
    simpa [fullResponseTraceLeading,fullResponseTraceLeadingBudget,fullResponseIdentityWaveBudget] using
      full_response_scaled_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure (ENNReal.ofReal p)
        (fullResponseIdentityWaveTerm M Q N weights) _ _ hc hh.2
  · have hh := full_response_active_wave_series_Lp M h hM hg Q hpast N hN weights hw p hp hp256
    have hc : 0 ≤ rootEdelta .full*3*(planarGradientCharge 40+1)*fullResponseTraceC1*
        Real.sqrt (densityMomentBudget (rootQ .full) 4 1232) := by
      unfold rootEdelta planarGradientCharge fullResponseTraceC1 rootTau
      positivity
    simpa [fullResponseTraceLeading,fullResponseTraceLeadingBudget,fullResponseActiveWaveBudget] using
      full_response_scaled_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure (ENNReal.ofReal p)
        (fullResponseActiveWaveTerm M Q N weights) _ _ hc hh.2

/-- Every actual full deterministic error component has its source norm budget. -/
theorem full_response_trace_error_component_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (b : Fin 4) :
    eLpNorm (fun ω => ∑' hk, fullResponseTraceError M Q N weights b hk ω)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (fullResponseTraceErrorBudget M.gamma p ((N:ℝ)-(Q.scale:ℝ)+1) b) := by
  have hprotected : ∀ n ≤ Q.scale-342, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    omega
  have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hc0 : 0 ≤ fullResponseTraceC0 := by unfold fullResponseTraceC0 rootTau; positivity
  have hc1 : 0 ≤ fullResponseTraceC1 := by unfold fullResponseTraceC1 rootTau; positivity
  have hγ := M.shellPrefix.gamma_pos.le
  have hD : (0:ℝ) ≤ (N:ℝ)-(Q.scale:ℝ)+1 := by exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  fin_cases b
  · have hh := full_response_trace_matrix_series_Lp M h hM hg Q p hp 377 (by norm_num)
      hprotected N hN weights hw
    simpa [fullResponseTraceError,fullResponseTraceErrorBudget,Int.cast_add,Int.cast_sub] using hh.2
  · have hh := full_response_density_series_coarse_Lp M h hM hg Q hpast p hp hp256
    simpa [fullResponseTraceError,fullResponseTraceErrorBudget] using
      full_response_scaled_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure (ENNReal.ofReal p)
        (fullResponseDensityTerm M Q) _ _ (mul_nonneg hE hc0) hh
  · have hh := full_response_correlated_series_Lp M h hM hg Q hpast N hN weights hw 0 p hp hp256
    have hc : 0 ≤ (rootEdelta .full*fullResponseTraceC1*M.gamma*
        (3:ℝ)^(2*M.gamma*((N:ℝ)-(Q.scale:ℝ)+1))/2)*((N:ℝ)-(Q.scale:ℝ)+1) := by positivity
    simpa [fullResponseTraceError,fullResponseTraceErrorBudget] using
      full_response_scaled_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure (ENNReal.ofReal p)
        (fullResponseCorrelatedTerm M Q N weights 0) _ _ hc hh.2
  · have hh := full_response_correlated_series_Lp M h hM hg Q hpast N hN weights hw 1 p hp hp256
    have hc : 0 ≤ rootEdelta .full*fullResponseTraceC1*M.gamma*
        (3:ℝ)^(2*M.gamma*((N:ℝ)-(Q.scale:ℝ)+1))/2 := by positivity
    simpa [fullResponseTraceError,fullResponseTraceErrorBudget] using
      full_response_scaled_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure (ENNReal.ofReal p)
        (fullResponseCorrelatedTerm M Q N weights 1) _ _ hc hh.2

end
end ASDExplicitGamma.Inverse
