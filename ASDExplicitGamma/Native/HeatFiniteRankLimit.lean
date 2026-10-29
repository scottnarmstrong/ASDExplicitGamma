module

public import ASDExplicitGamma.Gaussian.SeriesHeat
public import ASDExplicitGamma.Gaussian.SeriesPassage
public import ASDExplicitGamma.Gaussian.ModelHeatAverage
public import ASDExplicitGamma.Gaussian.BandHeat
public import ASDExplicitGamma.Inverse.SourceFramePhysical

/-! Fixed-operator finite-rank passage for the native Gaussian heat identity. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Filter MeasureTheory Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
open scoped Topology

/-- At a fixed Gaussian-series operator, the fast finite-rank heat averages and
their finite Hessian traces converge to the countable-series heat identity.
The operator is fixed throughout; this makes no uniform claim as a diffusivity
parameter in the operator tends to zero. -/
theorem nativeHeat_finiteRankPassage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (gaussianSeriesHeatAverage hA T Φ x)
        ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t) t ∧
      Tendsto (fun k => gaussianFastHeatAverage hA T Φ x k t) atTop
        (𝓝 (gaussianSeriesHeatAverage hA T Φ x t)) ∧
      Tendsto (fun k => gaussianFastHeatTraceAverage hA T Φ x k t) atTop
        (𝓝 (gaussianSeriesHeatTraceAverage hA T Φ x t)) := by
  have hTraceGrowth := hasPolynomiallyBoundedSecondDirectionalDerivative_of_C2Derivatives hΦ
  exact ⟨hasDerivAt_gaussianSeriesHeatAverage hA T Φ hΦ x ht,
    tendsto_gaussianFastHeatAverage hA T Φ hΦ x,
    tendsto_gaussianFastHeatTraceAverage hA T Φ hΦ.1 hTraceGrowth x t⟩

/-- The finite-rank heat average also converges after averaging over an older
coefficient law.  The product-space majorant keeps the old input and the fast
Gaussian envelope separate, so no uniform-integrability premise is added. -/
noncomputable def nativeHeatFastRandomBaseAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] E) (Φ : E → ℝ) (μ : Measure E) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ p : E × (ℕ → ℝ),
    Φ (p.1 + Real.sqrt t • T (gaussianFastPartialSumSequence hA k p.2))
    ∂(μ.prod standardGaussianInfinitePi)

/-- Finite-rank heat averages on the independent older/series product law
converge to the countable-series heat average.  In the native application,
`μ` is the pushforward of the actual cutoff law by the old-field restriction. -/
theorem nativeHeat_fastRandomBaseAverage_tendsto {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) μ)
    (t : ℝ) :
    Tendsto (fun k => nativeHeatFastRandomBaseAverage hA T Φ μ k t) atTop
      (𝓝 (randomBaseHeatAverage hA T μ Φ t)) := by
  classical
  rcases hΦ with ⟨hC2, C, hC, d, hvalue, _, _⟩
  have hGrowth : HasPolynomialGrowth Φ := ⟨C, hC, d, hvalue⟩
  let ρ := μ.prod standardGaussianInfinitePi
  let env : (ℕ → ℝ) → ℝ := gaussianFastEnvelope hA
  let bound : E × (ℕ → ℝ) → ℝ := fun p =>
    C * (1 + Real.sqrt t * ‖T‖) ^ d *
      ((1 + ‖p.1‖) ^ d * (1 + env p.2) ^ d)
  have hprod : Integrable
      (fun p : E × (ℕ → ℝ) => (1 + ‖p.1‖) ^ d * (1 + env p.2) ^ d) ρ := by
    exact (hμ d).mul_prod (integrable_fastEnvelope_polynomial hA d)
  have hboundInt : Integrable bound ρ := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      hprod.const_mul (C * (1 + Real.sqrt t * ‖T‖) ^ d)
  have hpartial : ∀ᵐ p ∂ρ, ∀ k,
      ‖gaussianFastPartialSumSequence hA k p.2‖ ≤ env p.2 := by
    have hγ := ae_norm_gaussianFastPartialSum_le_envelope hA
    have hmap : Measure.map Prod.snd ρ = standardGaussianInfinitePi := by
      simp [ρ]
    have hγ' : ∀ᵐ ω ∂Measure.map Prod.snd ρ,
        ∀ k, ‖gaussianFastPartialSumSequence hA k ω‖ ≤ env ω := by
      simpa [hmap] using hγ
    exact ae_of_ae_map measurable_snd.aemeasurable hγ'
  have hlimSeries : ∀ᵐ p ∂ρ,
      Tendsto (fun k => gaussianFastPartialSumSequence hA k p.2) atTop
        (𝓝 (gaussianSeriesLimit v hA p.2)) := by
    have hγ := ae_tendsto_gaussianSeriesLimit v hA
    have hmap : Measure.map Prod.snd ρ = standardGaussianInfinitePi := by
      simp [ρ]
    have hγ' : ∀ᵐ ω ∂Measure.map Prod.snd ρ,
        Tendsto (fun k => gaussianFastPartialSumSequence hA k ω) atTop
          (𝓝 (gaussianSeriesLimit v hA ω)) := by
      simpa [hmap] using hγ
    exact ae_of_ae_map measurable_snd.aemeasurable hγ'
  have hfastMeas (k : ℕ) : AEStronglyMeasurable
      (fun p : E × (ℕ → ℝ) =>
        Φ (p.1 + Real.sqrt t • T (gaussianFastPartialSumSequence hA k p.2))) ρ := by
    let n := gaussianFastIndex hA k
    have hpartialMeas : Measurable (fun ω : ℕ → ℝ => gaussianPartialSum v n ω) := by
      have hcont : Continuous (fun ω : ℕ → ℝ =>
          ∑ j ∈ Finset.range n, ω j • v j) := by
        apply continuous_finsetSum
        intro j hj
        exact (continuous_apply j).smul continuous_const
      simpa [gaussianPartialSum] using hcont.measurable
    have hTMeas : Measurable (fun p : E × (ℕ → ℝ) =>
        T (gaussianPartialSum v n p.2)) :=
      T.continuous.measurable.comp (hpartialMeas.comp measurable_snd)
    have hsmulMeas : Measurable (fun p : E × (ℕ → ℝ) =>
        Real.sqrt t • T (gaussianPartialSum v n p.2)) :=
      hTMeas.const_smul (Real.sqrt t)
    have hargMeas : Measurable (fun p : E × (ℕ → ℝ) =>
        p.1 + Real.sqrt t • T (gaussianPartialSum v n p.2)) := by
      exact measurable_fst.add hsmulMeas
    exact (hC2.continuous.measurable.comp hargMeas).aestronglyMeasurable
  have hfastBound : ∀ k, ∀ᵐ p ∂ρ,
      ‖Φ (p.1 + Real.sqrt t • T (gaussianFastPartialSumSequence hA k p.2))‖ ≤
        bound p := by
    intro k
    filter_upwards [hpartial] with p hp
    rw [Real.norm_eq_abs]
    have henv : 0 ≤ env p.2 := by
      dsimp [env, gaussianFastEnvelope, gaussianFastVariation]
      positivity
    have hT : ‖T (gaussianFastPartialSumSequence hA k p.2)‖ ≤
        ‖T‖ * env p.2 := by
      calc
        _ ≤ ‖T‖ * ‖gaussianFastPartialSumSequence hA k p.2‖ := T.le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hp k) (norm_nonneg _)
    have harg : 1 + ‖p.1 + Real.sqrt t •
        T (gaussianFastPartialSumSequence hA k p.2)‖ ≤
        (1 + Real.sqrt t * ‖T‖) * (1 + ‖p.1‖) * (1 + env p.2) := by
      have ht : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
      have hnorm := norm_add_le p.1
        (Real.sqrt t • T (gaussianFastPartialSumSequence hA k p.2))
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hnorm
      have hc : 0 ≤ Real.sqrt t * ‖T‖ := mul_nonneg ht (norm_nonneg T)
      have hmul : Real.sqrt t * ‖T (gaussianFastPartialSumSequence hA k p.2)‖ ≤
          Real.sqrt t * (‖T‖ * env p.2) := mul_le_mul_of_nonneg_left hT ht
      have hnorm' : 1 + ‖p.1 + Real.sqrt t •
          T (gaussianFastPartialSumSequence hA k p.2)‖ ≤
          1 + ‖p.1‖ + Real.sqrt t * (‖T‖ * env p.2) := by
        nlinarith [hnorm]
      have hbase : 1 + ‖p.1‖ ≤ (1 + ‖p.1‖) * (1 + env p.2) := by
        apply le_mul_of_one_le_right (by positivity)
        linarith
      have henv' : env p.2 ≤ (1 + ‖p.1‖) * (1 + env p.2) := by
        have hb : 0 ≤ ‖p.1‖ := norm_nonneg _
        nlinarith [mul_nonneg hb henv]
      have hscaled : Real.sqrt t * (‖T‖ * env p.2) ≤
          (Real.sqrt t * ‖T‖) * ((1 + ‖p.1‖) * (1 + env p.2)) := by
        calc
          Real.sqrt t * (‖T‖ * env p.2) =
              (Real.sqrt t * ‖T‖) * env p.2 := by ring
          _ ≤ (Real.sqrt t * ‖T‖) * ((1 + ‖p.1‖) * (1 + env p.2)) :=
            mul_le_mul_of_nonneg_left henv' hc
      calc
        1 + ‖p.1 + Real.sqrt t •
            T (gaussianFastPartialSumSequence hA k p.2)‖
          ≤ 1 + ‖p.1‖ + Real.sqrt t * (‖T‖ * env p.2) := hnorm'
        _ ≤ (1 + ‖p.1‖) * (1 + env p.2) +
            (Real.sqrt t * ‖T‖) * ((1 + ‖p.1‖) * (1 + env p.2)) := by
              nlinarith [hbase, hscaled]
        _ = (1 + Real.sqrt t * ‖T‖) *
            ((1 + ‖p.1‖) * (1 + env p.2)) := by ring
        _ = (1 + Real.sqrt t * ‖T‖) * (1 + ‖p.1‖) * (1 + env p.2) := by ring
    calc
      |Φ (p.1 + Real.sqrt t •
          T (gaussianFastPartialSumSequence hA k p.2))| ≤
        C * (1 + ‖p.1 + Real.sqrt t •
          T (gaussianFastPartialSumSequence hA k p.2)‖) ^ d := hvalue _
      _ ≤ C * ((1 + Real.sqrt t * ‖T‖) * (1 + ‖p.1‖) *
          (1 + env p.2)) ^ d := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact pow_le_pow_left₀ (by positivity) harg d
      _ = bound p := by
        dsimp [bound]
        rw [mul_pow, mul_pow]
        ring
  have hlim : ∀ᵐ p ∂ρ, Tendsto
      (fun k => Φ (p.1 + Real.sqrt t • T
        (gaussianFastPartialSumSequence hA k p.2))) atTop
      (𝓝 (Φ (gaussianSeriesHeatArgument hA T p.1 t p.2))) := by
    filter_upwards [hlimSeries] with p hp
    exact hC2.continuous.continuousAt.tendsto.comp
      ((continuous_const.add ((continuous_const : Continuous fun _ : V => Real.sqrt t)
        |>.smul T.continuous)).continuousAt.tendsto.comp hp)
  have hconv := tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall hfastMeas)
    (Filter.Eventually.of_forall hfastBound) hboundInt hlim
  have hlimitIntegrable : Integrable
      (fun p : E × (ℕ → ℝ) => Φ (gaussianSeriesHeatArgument hA T p.1 t p.2)) ρ :=
    integrable_randomBaseHeatIntegrand hA T μ hμ Φ hC2.continuous.measurable hGrowth t
  have hlimitEq :
      (∫ p : E × (ℕ → ℝ),
        Φ (gaussianSeriesHeatArgument hA T p.1 t p.2) ∂ρ) =
        randomBaseHeatAverage hA T μ Φ t := by
    simpa [ρ, randomBaseHeatAverage, gaussianSeriesHeatAverage,
      gaussianSeriesHeatArgument] using
      (integral_prod (fun p : E × (ℕ → ℝ) =>
        Φ (gaussianSeriesHeatArgument hA T p.1 t p.2)) hlimitIntegrable)
  rw [hlimitEq] at hconv
  simpa [nativeHeatFastRandomBaseAverage, ρ,
    gaussianSeriesHeatArgument, gaussianSeriesLimitE] using hconv

/-- For an actual finite fresh-shell band, the finite Gaussian-rank heat
averages converge to the model's expectation in the same pair of old/fresh
maps. The older-law moments follow from the cutoff model, and the band-law
identity is the actual independent-shell realization. -/
theorem nativeHeat_bandFastAverage_tendsto {b : ℕ} {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2)
    (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (hk : ∀ i, m < k i)
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K k) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A B : C(K, ℝ) →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (t : ℝ) :
    Tendsto
      (fun r => nativeHeatFastRandomBaseAverage hA (B.comp T) Φ
        (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map A) r t)
      atTop (𝓝 (bandModelAverage K M m k A B Φ t)) := by
  let μ := ((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map A
  have hμ : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) μ := by
    dsimp [μ]
    exact polynomial_moments_map _
      (integrable_polynomial_olderFieldLaw K M ell m hK) A
  have hgrowth : HasPolynomialGrowth Φ := by
    obtain ⟨_, C, hC, d, hvalue, _, _⟩ := hΦ
    exact ⟨C, hC, d, hvalue⟩
  have hlimit := nativeHeat_fastRandomBaseAverage_tendsto hA (B.comp T) Φ hΦ μ hμ t
  have heq := bandModelAverage_eq K M ell m hK k hk hA T hlaw A B Φ
    hΦ.1.continuous.measurable hgrowth t
  simpa [μ, heq] using hlimit

/-- The preceding finite-rank limit needs no chosen Gaussian-series witness:
the actual finite fresh band on the completed cutoff law supplies one. -/
theorem exists_nativeHeat_bandFastAverage_tendsto {b : ℕ} [NeZero b]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2)
    (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (hk : ∀ i, m < k i) (hki : Function.Injective k)
    (A B : C(K, ℝ) →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (t : ℝ) :
    ∃ (T : Gaussian.BandHilbert b →L[ℝ] C(K, ℝ))
      (v : ℕ → Gaussian.BandHilbert b)
      (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map (Gaussian.modelBand K k) =
        Gaussian.standardGaussianInfinitePi.map (Gaussian.gaussianSeriesLimitE hA T) ∧
      Tendsto
        (fun r => nativeHeatFastRandomBaseAverage hA (B.comp T) Φ
          (((Cutoff.cutoffSampleLaw M).toMeasure.map (Gaussian.olderField K m)).map A) r t)
        atTop (𝓝 (Gaussian.bandModelAverage K M m k A B Φ t)) := by
  obtain ⟨T, v, hA, hlaw⟩ :=
    Gaussian.exists_modelBand_realization K M h hM k hki
  exact ⟨T, v, hA, hlaw,
    nativeHeat_bandFastAverage_tendsto K M ell m hK k hk hA T hlaw A B Φ hΦ t⟩

/-- The actual finite-band passage keeps the source's true scalar frame and
returns both the countable-series heat identity and the pathwise frame
restoration estimate. -/
theorem exists_nativeHeat_bandFastAverage_tendsto_trueFrame {b : ℕ} [NeZero b]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2)
    (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (hk : ∀ i, m < k i) (hki : Function.Injective k)
    (A B : C(K, ℝ) →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (t : ℝ)
    (frameK frameM frameN : ℤ) (hframe : frameK ≤ frameM)
    (η : ℝ) (hη : 0 < η) :
    ∃ (T : Gaussian.BandHilbert b →L[ℝ] C(K, ℝ))
      (v : ℕ → Gaussian.BandHilbert b)
      (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map (Gaussian.modelBand K k) =
        Gaussian.standardGaussianInfinitePi.map (Gaussian.gaussianSeriesLimitE hA T) ∧
      Tendsto
        (fun r => nativeHeatFastRandomBaseAverage hA (B.comp T) Φ
          (((Cutoff.cutoffSampleLaw M).toMeasure.map (Gaussian.olderField K m)).map A) r t)
        atTop (𝓝 (Gaussian.bandModelAverage K M m k A B Φ t)) ∧
      (∀ x s, 0 < s →
        HasDerivAt (Gaussian.gaussianSeriesHeatAverage hA (B.comp T) Φ x)
          ((1 / 2 : ℝ) * Gaussian.gaussianSeriesHeatTraceAverage hA (B.comp T) Φ x s) s ∧
        Tendsto (fun r => Gaussian.gaussianFastHeatAverage hA (B.comp T) Φ x r s)
          atTop (𝓝 (Gaussian.gaussianSeriesHeatAverage hA (B.comp T) Φ x s)) ∧
        Tendsto (fun r => Gaussian.gaussianFastHeatTraceAverage hA (B.comp T) Φ x r s)
          atTop (𝓝 (Gaussian.gaussianSeriesHeatTraceAverage hA (B.comp T) Φ x s))) ∧
      ContinuousOn (Gaussian.bandModelAverage K M m k A B Φ) (Set.Ici 0) ∧
      ContinuousOn (fun s => (1 / 2 : ℝ) * Gaussian.bandModelAverage K M m k A B
        (Gaussian.modelCovarianceTrace Φ (fun j => B (T (v j)))) s) (Set.Ici 0) ∧
      (∀ s, s ∈ Set.Ioi 0 → HasDerivAt (Gaussian.bandModelAverage K M m k A B Φ)
        ((1 / 2 : ℝ) * Gaussian.bandModelAverage K M m k A B
          (Gaussian.modelCovarianceTrace Φ (fun j => B (T (v j)))) s) s) ∧
      HasDerivWithinAt (Gaussian.bandModelAverage K M m k A B Φ)
        ((1 / 2 : ℝ) * Gaussian.bandModelAverage K M m k A B
          (Gaussian.modelCovarianceTrace Φ (fun j => B (T (v j)))) 0) (Set.Ici 0) 0 ∧
      (∀ ω, cutoffTraceDefect M frameM frameN ω ≤
        ((Annealed.sigmaBar M frameM : ℝ) / (Annealed.sigmaBar M frameK : ℝ)) *
          ((1 + η) * traceDefect (cubeSet (originCube 2 frameN))
              (Cutoff.coefficientCutoff M.nu frameM ω).toFun
              (Annealed.sigmaBar M frameK : ℝ) +
            8 * (1 + 1 / η) * ((11 / 10 : ℝ) * M.gamma *
              (frameM - frameK : ℝ)) ^ 2)) := by
  obtain ⟨T, v, hA, hlaw, hconv⟩ :=
    exists_nativeHeat_bandFastAverage_tendsto K M h hM ell m hK k hk hki A B Φ hΦ t
  have hheat := Gaussian.c1On_bandModelAverage K M ell m hK k hk hA T hlaw A B Φ hΦ
  have hpoint : ∀ x s, 0 < s →
      HasDerivAt (Gaussian.gaussianSeriesHeatAverage hA (B.comp T) Φ x)
        ((1 / 2 : ℝ) * Gaussian.gaussianSeriesHeatTraceAverage hA (B.comp T) Φ x s) s ∧
      Tendsto (fun r => Gaussian.gaussianFastHeatAverage hA (B.comp T) Φ x r s)
        atTop (𝓝 (Gaussian.gaussianSeriesHeatAverage hA (B.comp T) Φ x s)) ∧
      Tendsto (fun r => Gaussian.gaussianFastHeatTraceAverage hA (B.comp T) Φ x r s)
        atTop (𝓝 (Gaussian.gaussianSeriesHeatTraceAverage hA (B.comp T) Φ x s)) := by
    intro x s hs
    exact nativeHeat_finiteRankPassage hA (B.comp T) Φ hΦ x hs
  refine ⟨T, v, hA, hlaw, hconv, hpoint, hheat.1, hheat.2.1, hheat.2.2.1,
    hheat.2.2.2, ?_⟩
  intro ω
  exact source_cutoff_pathwise_frame_map M frameK frameM frameN ω hframe η hη

end ASDExplicitGamma.Native
