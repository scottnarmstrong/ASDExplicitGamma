module

public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectation
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfile

/-! Actual depth-ten child geometry in the drift expectation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Gaussian Algsuperdiff.Section3 Numerics.Native
open scoped ENNReal NNReal
noncomputable section

/-- The normalized weight of each of the source's 9^10 refined children. -/
def heatVHEATDriftRefinedWeight : ℝ := (9^10:ℝ)⁻¹

/-- Literal translations of the actual depth-ten children to origin coordinates. -/
def heatVHEATDriftRefinedShift (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) : Vec 2 :=
  triadicCubeShift (nativeHeatQ3RefinedCarrierChild m i)

/-- The source's actual finite population has unit total normalized weight. -/
theorem heatVHEATDrift_refined_weights :
    0 ≤ heatVHEATDriftRefinedWeight ∧
    (∑ _i : nativeHeatQ3RefinedCarrierIndex,heatVHEATDriftRefinedWeight)=1 := by
  constructor
  · unfold heatVHEATDriftRefinedWeight
    positivity
  · rw [Finset.sum_const,Finset.card_univ,nativeHeatQ3RefinedCarrierIndex_card]
    norm_num [heatVHEATDriftRefinedWeight]

/-- The actual canonical drift family on the refined carrier translations.
The auxiliary coordinates share the one common Gaussian sequence. -/
def heatVHEATDriftRefinedSource
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) :=
  heatVHEATDriftSource Finset.univ (fun _ => heatVHEATDriftRefinedWeight)
    M h (m+1) t k (heatVHEATDriftRefinedShift m) g

/-- The corresponding literal common-frame average of the actual child traces. -/
def heatVHEATDriftRefinedAverage
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) :=
  heatRefinedTraceAverage Finset.univ (fun _ => heatVHEATDriftRefinedWeight)
    M (m+1) 9 t (heatVHEATDriftRefinedShift m) g

/-- Drift expectation specialized to the actual refined carrier's 9^10
translations and normalized weights. Gaussian coordinates are source data;
no independence, norm estimate, or bank estimate is a premise. The carrier
owner supplies its constructed center coordinates and their exact laws. -/
theorem nativeHeat_vheat_refined_drift_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ l<m+1,nativeInductionState M h l) (hstate : nativeInductionState M h (m+1))
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) (hgm : ∀ i,Measurable (g i))
    (v : nativeHeatQ3RefinedCarrierIndex → ℝ≥0)
    (hlaw : ∀ i,standardGaussianInfinitePi.map
      (fun ξ => g i ξ/(Annealed.sigmaBar M (m+1):ℝ))=gaussianReal 0 (v i)) :
    let μ := nativeHeatRemainderJointLaw M
    let A := heatVHEATDriftRefinedAverage M m t g
    let X := heatVHEATDriftSourceXExtended Finset.univ M (m+1) t (heatVHEATDriftRefinedShift m) g
    let F := heatRefinedRawEnvelope 9 (heatVHEATDriftAuxVariance Finset.univ v)
    X < ⊤ ∧ Integrable (heatVHEATDriftRefinedSource M h m t k g) μ ∧
    (∫ z,heatVHEATDriftRefinedSource M h m t k g z ∂μ) ≤
      (k:ℝ)*heatVHEATDriftE9 M*
        (2*(nativeHeatK:ℝ)*(3683/2500)+(nativeHeatM:ℝ)*(3683/2500)^2)*
        ((∫ z,A z^k ∂μ)+4*(∫ z,A z^(k-1) ∂μ))+
      heatVHEATDriftFirstLine k (heatVHEATDriftE9 M)
        nativeHeatK nativeHeatM (3683/2500) (3/10^46) X.toReal F := by
  exact nativeHeat_vheat_drift_configured_expectation M h hM hg (m+1) hpast hstate t ht k hk hk20
    Finset.univ (fun _ => heatVHEATDriftRefinedWeight)
    (fun _ _ => heatVHEATDrift_refined_weights.1) heatVHEATDrift_refined_weights.2
    (heatVHEATDriftRefinedShift m) g (fun i _ => hgm i) v (fun i _ => hlaw i)

end
end ASDExplicitGamma.Native
