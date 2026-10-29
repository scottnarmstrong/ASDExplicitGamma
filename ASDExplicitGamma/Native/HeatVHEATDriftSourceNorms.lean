module

public import ASDExplicitGamma.Native.HeatVHEATDriftNormMax
public import ASDExplicitGamma.Native.HeatRefinedFamilyProfiles

/-! Intrinsic norms of the actual source family, derived from proved model
profiles, before any conversion from extended norms to real quantities. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Gaussian Algsuperdiff.Section3
open scoped ENNReal NNReal
noncomputable section

/-- A finite common auxiliary variance selected from the actual marginal
laws. This maximizes variance only, never the physical rare factors. -/
def heatVHEATDriftAuxVariance {I : Type*} (s : Finset I) (v : I → ℝ≥0) : ℝ :=
  (s.sup v : ℝ≥0)

/-- The exact intrinsic child trace norm, still extended. -/
def heatVHEATDriftSourceXExtended {I : Type*}
    (s : Finset I) (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) : ℝ≥0∞ :=
  heatVHEATDriftXExtended (nativeHeatRemainderJointLaw M) s
    (fun i => heatRefinedTranslatedTrace M n 9 t (x i) (g i))

/-- Actual model profiles prove all full128 and heat20 norm inputs used by
the source expectation theorem. No trace or bank bound is a premise. The
auxiliary coordinates may be arbitrarily correlated. -/
theorem heatVHEATDrift_source_norms {I : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : t ≤ 1)
    (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i) (hw1 : ∑ i∈s,w i=1)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) (hgm : ∀ i∈s,Measurable (g i))
    (v : I → ℝ≥0)
    (hlaw : ∀ i∈s,standardGaussianInfinitePi.map
      (fun ξ => g i ξ/(Annealed.sigmaBar M n:ℝ))=gaussianReal 0 (v i)) :
    let μ := nativeHeatRemainderJointLaw M
    let X := heatVHEATDriftSourceXExtended s M n t x g
    let F := heatRefinedRawEnvelope 9 (heatVHEATDriftAuxVariance s v)
    X < ⊤ ∧
    (∀ i∈s,eLpNorm (heatRefinedTranslatedRare M n 9 t (x i)) 128 μ ≤ ENNReal.ofReal (3/10^46:ℝ)) ∧
    (∀ i∈s,eLpNorm (heatRefinedTranslatedTrace M n 9 t (x i) (g i)) 20 μ ≤ ENNReal.ofReal X.toReal) ∧
    eLpNorm (heatRefinedTraceAverage s w M n 9 t x g) 20 μ ≤ ENNReal.ofReal X.toReal ∧
    (∀ i∈s,eLpNorm (heatRefinedTranslatedTrace M n 9 t (x i) (g i)) 128 μ ≤ ENNReal.ofReal F) ∧
    eLpNorm (heatRefinedTraceAverage s w M n 9 t x g) 128 μ ≤ ENNReal.ofReal F := by
  let heatJointProbability : IsProbabilityMeasure (nativeHeatRemainderJointLaw M) :=
    inferInstanceAs (IsProbabilityMeasure ((Cutoff.cutoffSampleLaw M).toMeasure.prod standardGaussianInfinitePi))
  dsimp only
  have hT (i : I) (hi : i∈s) :=
    heat_refined_translated_trace_measurable_nonneg M n 9 t (x i) (g i) (hgm i hi)
  have hraw (i : I) (hi : i∈s) :
      eLpNorm (heatRefinedTranslatedTrace M n 9 t (x i) (g i)) 128 (nativeHeatRemainderJointLaw M) ≤
        ENNReal.ofReal (heatRefinedRawEnvelope 9 (heatVHEATDriftAuxVariance s v)) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0) (by norm_num)
      (hT i hi).1.aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofNat] using
      heat_refined_translated_raw_prime M h hM hg n 9 (by norm_num) hpast t ht
        (x i) (g i) (hgm i hi) (v i) (heatVHEATDriftAuxVariance s v) (hlaw i hi)
        (by exact_mod_cast (Finset.le_sup (f := v) hi))
  have hc := heatVHEATDrift_intrinsic_trace_caps (nativeHeatRemainderJointLaw M)
    s w hw hw1 (fun i => heatRefinedTranslatedTrace M n 9 t (x i) (g i))
    (fun i hi => (hT i hi).1.aestronglyMeasurable)
    (heatRefinedRawEnvelope 9 (heatVHEATDriftAuxVariance s v)) hraw
  refine ⟨hc.1,?_,hc.2.1,hc.2.2.1,hraw,hc.2.2.2⟩
  intro i hi
  have hr := heat_refined_translated_rare_profiles M h hM hg n 9 hpast t ht (x i)
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0) (by norm_num) hr.1.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofNat] using hr.2.2

end
end ASDExplicitGamma.Native
