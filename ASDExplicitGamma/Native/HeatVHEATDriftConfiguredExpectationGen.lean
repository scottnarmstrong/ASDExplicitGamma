module

public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectation
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficientsGen

/-! The `ns`-shell generalization of `HeatVHEATDriftConfiguredExpectation`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Gaussian Algsuperdiff.Section3 Numerics.Native
open scoped ENNReal NNReal
noncomputable section

variable (ns : ℕ)

theorem nativeHeat_vheat_drift_configured_expectation_Gen (hns : ns ≤ 1331) {I : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i) (hw1 : ∑ i∈s,w i=1)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) (hgm : ∀ i∈s,Measurable (g i))
    (v : I → ℝ≥0)
    (hlaw : ∀ i∈s,standardGaussianInfinitePi.map
      (fun ξ => g i ξ/(Annealed.sigmaBar M n:ℝ))=gaussianReal 0 (v i)) :
    let μ := nativeHeatRemainderJointLaw M
    let A := heatRefinedTraceAverage s w M n ns t x g
    let X := (heatVHEATDriftSourceXExtendedGen ns) s M n t x g
    let F := heatRefinedRawEnvelope ns (heatVHEATDriftAuxVariance s v)
    X < ⊤ ∧ Integrable ((heatVHEATDriftSourceGen ns) s w M h n t k x g) μ ∧
    (∫ z,(heatVHEATDriftSourceGen ns) s w M h n t k x g z ∂μ) ≤
      (k:ℝ)*(heatVHEATDriftEGen ns) M*
        (2*(nativeHeatK:ℝ)*(3683/2500)+(nativeHeatM:ℝ)*(3683/2500)^2)*
        ((∫ z,A z^k ∂μ)+4*(∫ z,A z^(k-1) ∂μ))+
      heatVHEATDriftFirstLine k ((heatVHEATDriftEGen ns) M)
        nativeHeatK nativeHeatM (3683/2500) (3/10^46) X.toReal F := by
  dsimp only
  have hf := (nativeHeat_vheat_drift_expectation_Gen ns hns) M h hM hg n hpast hstate t ht k hk hk20
    s w hw hw1 x g hgm v hlaw
  have he : 0 ≤ (heatVHEATDriftEGen ns) M := by
    unfold heatVHEATDriftEGen
    exact mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA (z) : 0 ≤ heatRefinedTraceAverage s w M n ns t x g z :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi)
      ((heat_refined_translated_trace_measurable_nonneg M n ns t (x i) (g i) (hgm i hi)).2 z))
  have hc := (heatVHEATDrift_source_sums_le_configured_Gen ns) n
  refine ⟨hf.1,hf.2.1,hf.2.2.trans ?_⟩
  apply heatVHEATDrift_payment_mono_coefficients
    k ((heatVHEATDriftEGen ns) M) ((heatVHEATDriftKActualGen ns) n) (heatVHEATDriftCActualGen ns)
    nativeHeatK nativeHeatM (3683/2500) (3/10^46)
    ((heatVHEATDriftSourceXExtendedGen ns) s M n t x g).toReal
    (heatRefinedRawEnvelope ns (heatVHEATDriftAuxVariance s v)) _
    he (by norm_num) (by norm_num) ENNReal.toReal_nonneg (sq_nonneg _)
    (add_nonneg (integral_nonneg (fun z => pow_nonneg (hA z) _))
      (mul_nonneg (by norm_num) (integral_nonneg (fun z => pow_nonneg (hA z) _)))) hc.1 hc.2

end
end ASDExplicitGamma.Native
