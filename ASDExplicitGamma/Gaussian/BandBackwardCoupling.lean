module

public import ASDExplicitGamma.Gaussian.ModelCoupling
public import ASDExplicitGamma.Gaussian.BandHeat

/-! # Coupling the exact backward identity to the completed cutoff model -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The literal actual-medium expectation of an independent auxiliary backward test. -/
noncomputable def bandModelBackwardAverage {b : ℕ} {W X : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (m : ℤ) (k : Fin b → ℤ)
    (P : C(K, ℝ) →L[ℝ] X) {w : ℕ → W} (hB : Summable (fun j => ‖w j‖ ^ 2))
    (S : W →L[ℝ] X) (Φ : X → ℝ) (θ t : ℝ) : ℝ :=
  bandModelAverage K M m k P P (backwardTest hB S Φ θ t) t

/-- Both actual factors retain their exact completed cutoff law. The auxiliary factor is an
independent copy, and no independence between a center and its remainder is introduced. -/
theorem bandModelBackwardAverage_eq {b : ℕ} {W X : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (hk : ∀ i, m < k i)
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K k) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (P : C(K, ℝ) →L[ℝ] X) {w : ℕ → W} (hB : Summable (fun j => ‖w j‖ ^ 2))
    (S : W →L[ℝ] X) {Φ : X → ℝ} (hΦcont : Continuous Φ) (hΦpoly : HasPolynomialGrowth Φ)
    (θ : ℝ) :
    bandModelBackwardAverage K M m k P hB S Φ θ =
      backwardAverage hA (P.comp T) hB S
        (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map P) Φ θ := by
  funext t
  let Z := gaussianSeriesLimitE hB S
  let a := Real.sqrt ((1 + θ) * (1 - t))
  have hZ : StronglyMeasurable Z := stronglyMeasurable_gaussianSeriesLimitE hB S
  have hm (d : ℕ) : Integrable (fun ω => (1 + ‖Z ω‖) ^ d) standardGaussianInfinitePi := by
    have hz : MemLp Z ((d + 2 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi := by
      convert memLp_gaussianSeriesLimitE hB S (p := (d + 2 : ℕ))
        (by exact_mod_cast (show 2 ≤ d + 2 by omega)) using 1
      simp [ENNReal.ofReal_add]
    exact integrable_one_add_norm_pow_of_memLp hz
  have hsm := integrable_scaled_moments standardGaussianInfinitePi Z hZ hm a
  have hsc := hZ.const_smul a
  have hGcont : Continuous (backwardTest hB S Φ θ t) :=
    continuous_integral_translate standardGaussianInfinitePi (fun ω => a • Z ω) hsc hsm hΦcont
      (by obtain ⟨C, hC, d, hb⟩ := hΦpoly
          exact ⟨C, hC, d, fun x => by simpa only [Real.norm_eq_abs] using hb x⟩)
  have hGpoly : HasPolynomialGrowth (backwardTest hB S Φ θ t) :=
    polynomial_growth_integral_translate standardGaussianInfinitePi (fun ω => a • Z ω) hsm hΦpoly
  let ν := (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map P)
  have hν := polynomial_moments_map _ (integrable_polynomial_olderFieldLaw K M ell m hK) P
  calc
    bandModelBackwardAverage K M m k P hB S Φ θ t =
        randomBaseHeatAverage hA (P.comp T) ν (backwardTest hB S Φ θ t) t :=
      bandModelAverage_eq K M ell m hK k hk hA T hlaw P P _ hGcont.measurable hGpoly t
    _ = backwardAverage hA (P.comp T) hB S ν Φ θ t :=
      (integral_prod _ (integrable_randomBaseHeatIntegrand hA (P.comp T) ν hν _ hGcont.measurable hGpoly t)).symm

end ASDExplicitGamma.Gaussian
