module

public import ASDExplicitGamma.Native.HeatRefinedAugmentedRaw
public import ASDExplicitGamma.Native.HeatRemainderMoments
public import Mathlib.MeasureTheory.Measure.Prod

/-! All translated descendants live on the SAME physical/auxiliary law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian
open scoped ENNReal
noncomputable section

def heatRefinedJointShift (x : Vec 2) (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    Cutoff.CutoffSample 2 × (ℕ → ℝ) := (Cutoff.translateCutoffSample x z.1,z.2)

/-- Actual trace of a translated refined descendant with its own auxiliary
coordinate. The entire family uses one physical sample and one Gaussian vector. -/
def heatRefinedTranslatedTrace (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (x : Vec 2) (g : (ℕ → ℝ) → ℝ) (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
    (heatRefinedObserverShear (n-1) n height t (Cutoff.translateCutoffSample x z.1) (g z.2))

/-- The ORIGINAL rare remainder at this descendant's translated parent. -/
def heatRefinedTranslatedRare (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (x : Vec 2) (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  nativeSourceBandRemainder M n height t (Cutoff.translateCutoffSample x z.1)

theorem heat_refined_joint_shift_preserving (M : ABKModel 2) (x : Vec 2) :
    MeasurePreserving (heatRefinedJointShift x) (nativeHeatRemainderJointLaw M)
      (nativeHeatRemainderJointLaw M) := by
  have hm : MeasurePreserving (Cutoff.translateCutoffSample x)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    ⟨Cutoff.measurable_translateCutoffSample x,Cutoff.map_translateCutoffSample_cutoffSampleLaw M x⟩
  exact hm.prod (MeasurePreserving.id standardGaussianInfinitePi)

/-- Measurability and positivity of every actual translated, sheared trace. -/
theorem heat_refined_translated_trace_measurable_nonneg
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (x : Vec 2)
    (g : (ℕ → ℝ) → ℝ) (hg : Measurable g) :
    Measurable (heatRefinedTranslatedTrace M n height t x g) ∧
      ∀ z,0 ≤ heatRefinedTranslatedTrace M n height t x g z := by
  have hc : Measurable (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      ContinuousMap.const (closure (cubeSet (originCube 2 (n-1)))) (g z.2)) :=
    (ContinuousLinearMap.const (R := ℝ) (M := ℝ) (closure (cubeSet (originCube 2 (n-1))))).continuous.measurable.comp
      (hg.comp measurable_snd)
  have hp : Measurable (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      parentBoundaryObserverBandScalar (n-1) n height t (Cutoff.translateCutoffSample x z.1)) := (parent_boundary_observer_band_scalar_measurable (n-1) n height t).comp
    ((Cutoff.measurable_translateCutoffSample x).comp measurable_fst)
  refine ⟨?_,?_⟩
  · exact (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp (hp.add hc)
  · intro z
    exact modelTraceObservable_nonneg (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 _

/-- A marginal translation preserves its norm without asserting independence
of any pair of descendants. -/
theorem heat_refined_translated_trace_norm_eq
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (x : Vec 2)
    (g : (ℕ → ℝ) → ℝ) (hg : Measurable g) (p : ℝ≥0∞) :
    eLpNorm (heatRefinedTranslatedTrace M n height t x g) p (nativeHeatRemainderJointLaw M) =
      eLpNorm (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
        modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
          (heatRefinedObserverShear (n-1) n height t z.1 (g z.2))) p (nativeHeatRemainderJointLaw M) := by
  let T := fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
    modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
      (heatRefinedObserverShear (n-1) n height t z.1 (g z.2))
  have hm : Measurable T := by
    have hc : Measurable (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
        ContinuousMap.const (closure (cubeSet (originCube 2 (n-1)))) (g z.2)) :=
      (ContinuousLinearMap.const (R := ℝ) (M := ℝ) (closure (cubeSet (originCube 2 (n-1))))).continuous.measurable.comp
        (hg.comp measurable_snd)
    exact (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
      (((parent_boundary_observer_band_scalar_measurable (n-1) n height t).comp measurable_fst).add hc)
  change eLpNorm (T ∘ heatRefinedJointShift x) p (nativeHeatRemainderJointLaw M) = _
  exact eLpNorm_comp_measurePreserving hm.aestronglyMeasurable (heat_refined_joint_shift_preserving M x)

/-- Every translated marginal uses the same original reserve, unchanged on
the enlarged law and without a population maximum. -/
theorem heat_refined_translated_rare_profiles
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1) (x : Vec 2) :
    Measurable (heatRefinedTranslatedRare M n height t x) ∧
    (∀ z,0 ≤ heatRefinedTranslatedRare M n height t x z) ∧
    eLpNorm' (heatRefinedTranslatedRare M n height t x) 128 (nativeHeatRemainderJointLaw M) ≤
      ENNReal.ofReal (3/10^46:ℝ) := by
  have hb := native_source_band_history_rare_split M h hM hg n height hpast t ht
  have hm : Measurable (heatRefinedTranslatedRare M n height t x) :=
    hb.2.1.comp ((Cutoff.measurable_translateCutoffSample x).comp measurable_fst)
  have hshift : MeasurePreserving (Cutoff.translateCutoffSample x)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    ⟨Cutoff.measurable_translateCutoffSample x,Cutoff.map_translateCutoffSample_cutoffSampleLaw M x⟩
  have hn := eLpNorm_comp_measurePreserving (p := (128:ℝ≥0∞)) hb.2.1.aestronglyMeasurable
    (hshift.comp (measurePreserving_fst (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (ν := standardGaussianInfinitePi)))
  have hc : eLpNorm (heatRefinedTranslatedRare M n height t x) 128
      (nativeHeatRemainderJointLaw M) ≤ ENNReal.ofReal (3/10^46:ℝ) := hn.le.trans hb.2.2.2.1
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0) (by norm_num) hm.aestronglyMeasurable] at hc
  exact ⟨hm,fun z => hb.2.2.1 _,by simpa only [ENNReal.toReal_ofNat] using hc⟩

end
end ASDExplicitGamma.Native
