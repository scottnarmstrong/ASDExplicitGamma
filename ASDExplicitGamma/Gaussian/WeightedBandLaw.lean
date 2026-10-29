module

public import ASDExplicitGamma.Gaussian.FiniteFactorLaw

/-! # Actual-law realization for deterministically attenuated shell bands -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-- The literal deterministic weighted sum of actual shell restrictions. -/
noncomputable def modelWeightedBand {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (k : Fin b → ℤ) (w : Fin b → ℝ) (ω : Cutoff.CutoffSample 2) : C(K, ℝ) :=
  ∑ i, w i • shellFieldScalarRestriction K (ω.1 (k i))

theorem measurable_modelWeightedBand {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (k : Fin b → ℤ) (w : Fin b → ℝ) : Measurable (modelWeightedBand K k w) := by
  apply Finset.measurable_sum
  intro i hi
  exact ((measurable_shellFieldScalarRestriction K).comp
    ((measurable_pi_apply (k i)).comp measurable_subtype_coe)).const_smul (w i)

/-- Deterministic attenuations act on the physical factors while retaining the independent
shell law. No premise asserting the law of the weighted band is required. -/
theorem modelWeightedBand_law_of_factors {b : ℕ} [NeZero b]
    (V : Fin b → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, CompleteSpace (V i)] [∀ i, SecondCountableTopology (V i)]
    [∀ i, MeasurableSpace (V i)] [∀ i, BorelSpace (V i)]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    (T : ∀ i, V i →L[ℝ] C(K, ℝ)) (v : ∀ i, ℕ → V i)
    (hv : ∀ i, Summable (fun j => ‖v i j‖ ^ 2))
    (hlaw : ∀ i, (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => shellFieldScalarRestriction K (ω.1 (k i))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE (hv i) (T i))) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map (modelWeightedBand K k w) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE (finiteDirections_summable V v hv)
        (finiteFactor V (fun i => w i • T i))) := by
  classical
  let A := finiteFactor V (fun i => w i • T i)
  let d := finiteDirections V v
  have hd : Summable (fun j => ‖d j‖ ^ 2) := finiteDirections_summable V v hv
  apply measure_eq_of_continuousMap_eval_linearCombination
  intro ι _ x t
  let L : C(K, ℝ) →L[ℝ] ℝ := ∑ i, t i • ContinuousMap.evalCLM ℝ (x i)
  let Li (i : Fin b) : C(K, ℝ) →L[ℝ] ℝ := w i • L
  have hL : (continuousMapEvalLinearCombination ι x t) = L := by
    funext f
    simp only [continuousMapEvalLinearCombination, L, sum_apply, smul_apply, smul_eq_mul,
      ContinuousMap.evalCLM_apply]
  rw [hL, Measure.map_map L.continuous.measurable (measurable_modelWeightedBand K k w),
    Measure.map_map L.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE hd A).measurable]
  have hi := (iIndepFun_shellRestrictions K M k hk).comp
    (fun i => (Li i : C(K, ℝ) → ℝ)) (fun i => (Li i).continuous.measurable)
  let s : Fin b → ℝ≥0 := fun i => Real.toNNReal (∑' j, (Li i (T i (v i j))) ^ 2)
  have hs (i : Fin b) : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => Li i (shellFieldScalarRestriction K (ω.1 (k i)))) = gaussianReal 0 (s i) := by
    have hm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 (k i))) :=
      (measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (k i)).comp measurable_subtype_coe)
    have hh := congrArg (fun ν : Measure C(K, ℝ) => ν.map (Li i)) (hlaw i)
    rw [Measure.map_map (Li i).continuous.measurable hm,
      Measure.map_map (Li i).continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE (hv i) (T i)).measurable] at hh
    exact hh.trans (map_gaussianSeriesLimitE_linear (hv i) (T i) (Li i))
  have hsum := independent_gaussian_sum_law (Cutoff.cutoffSampleLaw M).toMeasure
    (fun i ω => Li i (shellFieldScalarRestriction K (ω.1 (k i)))) s
    (fun i => (Li i).continuous.measurable.comp ((measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (k i)).comp measurable_subtype_coe))) hi hs
  have he : (fun ω => L (modelWeightedBand K k w ω)) =
      fun ω => ∑ i, Li i (shellFieldScalarRestriction K (ω.1 (k i))) := by
    funext ω
    simp only [modelWeightedBand, map_sum, map_smul, Li, smul_apply]
  simp only [Function.comp_def]
  rw [he, hsum, map_gaussianSeriesLimitE_linear hd A L]
  congr 2
  dsimp only [s, A, d]
  rw [finiteFactor_covariance V v hv (fun i => w i • T i) L,
    Real.toNNReal_sum_of_nonneg (fun i _ => tsum_nonneg fun j => sq_nonneg _)]
  simp only [Li, smul_apply, map_smul]

end ASDExplicitGamma.Gaussian
