module

public import ASDExplicitGamma.Native.HeatRefinedTranslatedLaw
public import ASDExplicitGamma.Native.HeatRemainderAverageNorm

/-! Actual correlated descendant profiles on the common enlarged law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3 Gaussian Numerics.Native
open scoped ENNReal NNReal BigOperators
noncomputable section

/-- Full-response raw envelope after auxiliary Gaussian augmentation. -/
def heatRefinedRawEnvelope (height : ℕ) (V : ℝ) : ℝ :=
  (Real.sqrt ((nativeHeatRQ:ℝ)*nativeSourceGenericFullResponseCap (17/50000) (height+1))+
    Real.sqrt (2*((3683/2500:ℝ)+3/10^46)*255*V))^2

/-- The actual spatial trace average, before averaging the auxiliary law. -/
def heatRefinedTraceAverage {I : Type*} (s : Finset I) (w : I → ℝ)
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  ∑ i ∈ s,w i*heatRefinedTranslatedTrace M n height t (x i) (g i) z

/-- Actual marginal full128 cap, with no response estimate as an assumption. -/
theorem heat_refined_translated_raw_prime
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hh : height ≤ 1331)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1)
    (x : Vec 2) (g : (ℕ → ℝ) → ℝ) (hgm : Measurable g) (v : ℝ≥0) (V : ℝ)
    (hlaw : standardGaussianInfinitePi.map (fun ξ => g ξ/(Annealed.sigmaBar M n:ℝ)) = gaussianReal 0 v)
    (hv : (v:ℝ) ≤ V) :
    eLpNorm' (heatRefinedTranslatedTrace M n height t x g) 128 (nativeHeatRemainderJointLaw M) ≤
      ENNReal.ofReal (heatRefinedRawEnvelope height V) := by
  have hc := heat_refined_auxiliary_raw_L128 M h hM hg n height hh hpast t ht g hgm v hlaw
  rw [←heat_refined_translated_trace_norm_eq M n height t x g hgm 128] at hc
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0) (by norm_num)
    (heat_refined_translated_trace_measurable_nonneg M n height t x g hgm).1.aestronglyMeasurable] at hc
  apply (show eLpNorm' _ 128 _ ≤ _ from hc).trans
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (add_le_add_right (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv (by positivity : (0:ℝ) ≤ 2*((3683/2500:ℝ)+3/10^46)*255))) _) 2

/-- Measurability, positivity and the raw cap of the literal spatial average.
All descendants may share both noises and every inverse weight. -/
theorem heat_refined_average_profiles {I : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hh : height ≤ 1331)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1)
    (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s,0 ≤ w i) (hw1 : ∑ i ∈ s,w i=1)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) (hgm : ∀ i ∈ s,Measurable (g i))
    (v : I → ℝ≥0) (V : ℝ)
    (hlaw : ∀ i ∈ s,standardGaussianInfinitePi.map (fun ξ => g i ξ/(Annealed.sigmaBar M n:ℝ)) = gaussianReal 0 (v i))
    (hv : ∀ i ∈ s,(v i:ℝ) ≤ V) :
    Measurable (heatRefinedTraceAverage s w M n height t x g) ∧
    (∀ z,0 ≤ heatRefinedTraceAverage s w M n height t x g z) ∧
    eLpNorm' (heatRefinedTraceAverage s w M n height t x g) 128 (nativeHeatRemainderJointLaw M) ≤
      ENNReal.ofReal (heatRefinedRawEnvelope height V) := by
  have hT (i : I) (hi : i ∈ s) :=
    heat_refined_translated_trace_measurable_nonneg M n height t (x i) (g i) (hgm i hi)
  refine ⟨?_,?_,?_⟩
  · exact Finset.measurable_sum s (fun i hi => (hT i hi).1.const_mul (w i))
  · intro z
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) ((hT i hi).2 z)
  · exact heat_remainder_average_prime_cap (nativeHeatRemainderJointLaw M) s w hw hw1 _
      (fun i hi => (hT i hi).1.aestronglyMeasurable) 128 (by norm_num) _
      (fun i hi => heat_refined_translated_raw_prime M h hM hg n height hh hpast t ht
        (x i) (g i) (hgm i hi) (v i) V (hlaw i hi) (hv i hi))

end
end ASDExplicitGamma.Native
