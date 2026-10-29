module

public import ASDExplicitGamma.Gaussian.FiniteHilbertFactor
public import ASDExplicitGamma.Gaussian.BandModelLaw

/-! # Actual finite-band law for heterogeneous Hilbert factors -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-- Exact independent-shell laws assemble into the direct-sum Hilbert series law. -/
theorem modelBand_law_of_factors {b : ℕ} [NeZero b]
    (V : Fin b → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, CompleteSpace (V i)] [∀ i, SecondCountableTopology (V i)]
    [∀ i, MeasurableSpace (V i)] [∀ i, BorelSpace (V i)]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2)
    (k : Fin b → ℤ) (hk : Function.Injective k)
    (T : ∀ i, V i →L[ℝ] C(K, ℝ)) (v : ∀ i, ℕ → V i)
    (hv : ∀ i, Summable (fun j => ‖v i j‖ ^ 2))
    (hlaw : ∀ i, (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => shellFieldScalarRestriction K (ω.1 (k i))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE (hv i) (T i))) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K k) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE (finiteDirections_summable V v hv)
        (finiteFactor V T)) := by
  classical
  let A := finiteFactor V T
  let w := finiteDirections V v
  have hw : Summable (fun j => ‖w j‖ ^ 2) := finiteDirections_summable V v hv
  apply measure_eq_of_continuousMap_eval_linearCombination
  intro ι _ x t
  let L : C(K, ℝ) →L[ℝ] ℝ := ∑ i, t i • ContinuousMap.evalCLM ℝ (x i)
  have hL : (continuousMapEvalLinearCombination ι x t) = L := by
    funext f
    simp only [continuousMapEvalLinearCombination, L, sum_apply, smul_apply, smul_eq_mul,
      ContinuousMap.evalCLM_apply]
  rw [hL, Measure.map_map L.continuous.measurable (measurable_modelBand K k),
    Measure.map_map L.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE hw A).measurable]
  have hi := (iIndepFun_shellRestrictions K M k hk).comp
    (fun _ => L) (fun _ => L.continuous.measurable)
  let s : Fin b → ℝ≥0 := fun i => Real.toNNReal (∑' j, (L (T i (v i j))) ^ 2)
  have hs (i : Fin b) : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => L (shellFieldScalarRestriction K (ω.1 (k i)))) = gaussianReal 0 (s i) := by
    have hm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 (k i))) :=
      (measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (k i)).comp measurable_subtype_coe)
    have hh := congrArg (fun ν : Measure C(K, ℝ) => ν.map L) (hlaw i)
    rw [Measure.map_map L.continuous.measurable hm,
      Measure.map_map L.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE (hv i) (T i)).measurable] at hh
    exact hh.trans (map_gaussianSeriesLimitE_linear (hv i) (T i) L)
  have hsum := independent_gaussian_sum_law (Cutoff.cutoffSampleLaw M).toMeasure
    (fun i ω => L (shellFieldScalarRestriction K (ω.1 (k i)))) s
    (fun i => L.continuous.measurable.comp ((measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (k i)).comp measurable_subtype_coe))) hi hs
  have he : (fun ω => L (modelBand K k ω)) =
      fun ω => ∑ i, L (shellFieldScalarRestriction K (ω.1 (k i))) := by
    funext ω
    exact map_sum L _ _
  simp only [Function.comp_def]
  rw [he, hsum]
  have hseries := map_gaussianSeriesLimitE_linear hw A L
  rw [hseries]
  congr 2
  dsimp only [s, A, w]
  rw [finiteFactor_covariance V v hv T L, Real.toNNReal_sum_of_nonneg (fun i _ => tsum_nonneg fun j => sq_nonneg _)]


end ASDExplicitGamma.Gaussian
