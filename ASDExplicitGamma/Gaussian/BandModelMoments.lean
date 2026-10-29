module

public import ASDExplicitGamma.Gaussian.ModelMoments
public import ASDExplicitGamma.Gaussian.BandHeat

/-! # Polynomial tests have all finite moments along mapped actual insertions -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The fresh field has all finite moments on the actual completed law, by its exact law. -/
theorem memLp_band_of_law {b : ℕ}
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (k : Fin b → ℤ)
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (modelBand K k) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    {p : ℝ} (hp : 2 ≤ p) :
    MemLp (modelBand K k)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi : MemLp (id : C(K, ℝ) → C(K, ℝ)) (ENNReal.ofReal p)
      (standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)) := by
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.aemeasurable).mpr
      (memLp_gaussianSeriesLimitE hA T hp)
  rw [← hlaw] at hi
  exact hi.comp_of_map (measurable_modelBand K k).aemeasurable

/-- Mapped model tests require no new moment hypothesis. -/
theorem memLp_bandModel_test {b : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell)) (k : Fin b → ℤ)
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (modelBand K k) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A B : C(K, ℝ) →L[ℝ] E) (Φ : E → ℝ) (hΦ : Measurable Φ) (hg : HasPolynomialGrowth Φ)
    (t : ℝ) {p : ℝ} (hp : 2 ≤ p) :
    MemLp (fun ω : Cutoff.CutoffSample 2 => Φ (A (olderField K m ω) +
      Real.sqrt t • B (modelBand K k ω)))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply memLp_polynomial _ _
    ((A.continuous.measurable.comp (measurable_olderField K ell m hK)).add
      ((B.continuous.measurable.comp (measurable_modelBand K k)).const_smul (Real.sqrt t)))
    (fun q hq => ((memLp_olderField K M ell m hK (by linarith : 1 ≤ q)).continuousLinearMap_comp A).add
      (((memLp_band_of_law K M k hA T hlaw hq).continuousLinearMap_comp B).const_smul (Real.sqrt t)))
    Φ hΦ hg hp

end ASDExplicitGamma.Gaussian
