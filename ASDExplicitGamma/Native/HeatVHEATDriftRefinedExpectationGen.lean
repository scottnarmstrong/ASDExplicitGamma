module

public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectation
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
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfileGen

/-! The `ns`-shell generalization of `HeatVHEATDriftRefinedExpectation`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Gaussian Algsuperdiff.Section3 Numerics.Native
open scoped ENNReal NNReal
noncomputable section

variable (ns : ℕ)

def heatVHEATDriftRefinedSourceGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) :=
  (heatVHEATDriftSourceGen ns) Finset.univ (fun _ => heatVHEATDriftRefinedWeight)
    M h (m+1) t k (heatVHEATDriftRefinedShift m) g

/-- The corresponding literal common-frame average of the actual child traces. -/
def heatVHEATDriftRefinedAverageGen
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) :=
  heatRefinedTraceAverage Finset.univ (fun _ => heatVHEATDriftRefinedWeight)
    M (m+1) ns t (heatVHEATDriftRefinedShift m) g

/-- Drift expectation specialized to the actual refined carrier's 9^10
translations and normalized weights. Gaussian coordinates are source data;
no independence, norm estimate, or bank estimate is a premise. The carrier
owner supplies its constructed center coordinates and their exact laws. -/
theorem nativeHeat_vheat_refined_drift_expectation_Gen (hns : ns ≤ 1331)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ l<m+1,nativeInductionState M h l) (hstate : nativeInductionState M h (m+1))
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) (hgm : ∀ i,Measurable (g i))
    (v : nativeHeatQ3RefinedCarrierIndex → ℝ≥0)
    (hlaw : ∀ i,standardGaussianInfinitePi.map
      (fun ξ => g i ξ/(Annealed.sigmaBar M (m+1):ℝ))=gaussianReal 0 (v i)) :
    let μ := nativeHeatRemainderJointLaw M
    let A := (heatVHEATDriftRefinedAverageGen ns) M m t g
    let X := (heatVHEATDriftSourceXExtendedGen ns) Finset.univ M (m+1) t (heatVHEATDriftRefinedShift m) g
    let F := heatRefinedRawEnvelope ns (heatVHEATDriftAuxVariance Finset.univ v)
    X < ⊤ ∧ Integrable ((heatVHEATDriftRefinedSourceGen ns) M h m t k g) μ ∧
    (∫ z,(heatVHEATDriftRefinedSourceGen ns) M h m t k g z ∂μ) ≤
      (k:ℝ)*(heatVHEATDriftEGen ns) M*
        (2*(nativeHeatK:ℝ)*(3683/2500)+(nativeHeatM:ℝ)*(3683/2500)^2)*
        ((∫ z,A z^k ∂μ)+4*(∫ z,A z^(k-1) ∂μ))+
      heatVHEATDriftFirstLine k ((heatVHEATDriftEGen ns) M)
        nativeHeatK nativeHeatM (3683/2500) (3/10^46) X.toReal F := by
  exact (nativeHeat_vheat_drift_configured_expectation_Gen ns hns) M h hM hg (m+1) hpast hstate t ht k hk hk20
    Finset.univ (fun _ => heatVHEATDriftRefinedWeight)
    (fun _ _ => heatVHEATDrift_refined_weights.1) heatVHEATDrift_refined_weights.2
    (heatVHEATDriftRefinedShift m) g (fun i _ => hgm i) v (fun i _ => hlaw i)

end
end ASDExplicitGamma.Native
