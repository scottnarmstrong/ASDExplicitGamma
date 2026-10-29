module

public import ASDExplicitGamma.Gaussian.BandHeat
public import ASDExplicitGamma.Gaussian.BandModelMoments
public import ASDExplicitGamma.Gaussian.FiniteFactorLaw

/-! # Weighted finite fresh bands: shell `i` enters with amplitude `c i`

The heat calculus of `BandHeat` for a band `∑ i, c i • shell_i` (all amplitudes real). Used for
attenuation vectors in which the shells are not attenuated simultaneously. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-- The weighted finite band of physical shell fields. -/
noncomputable def modelBandW {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (k : Fin b → ℤ) (c : Fin b → ℝ) (ω : Cutoff.CutoffSample 2) : C(K, ℝ) :=
  ∑ i, c i • shellFieldScalarRestriction K (ω.1 (k i))

theorem measurable_modelBandW {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (k : Fin b → ℤ) (c : Fin b → ℝ) : Measurable (modelBandW K k c) :=
  Finset.measurable_sum _ fun i _ => ((measurable_shellFieldScalarRestriction K).comp
    ((measurable_pi_apply (k i)).comp measurable_subtype_coe)).const_smul (c i)

/-- A weighted fresh finite band is independent of the entire completed older field. -/
theorem indepFun_olderField_bandW {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (c : Fin b → ℝ) (hk : ∀ i, m < k i) :
    IndepFun (olderField K m) (modelBandW K k c) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let X : Cutoff.ShellSeq 2 → C(K, ℝ) := fun ω =>
    ∑' r : ℕ, shellFieldScalarRestriction K (ω (m - (r : ℤ)))
  let Y : Cutoff.ShellSeq 2 → C(K, ℝ) := fun ω =>
    ∑ i, c i • shellFieldScalarRestriction K (ω (k i))
  have hX : @Measurable _ _ (Cutoff.shellIndexSigma (Iic m)) _ X := by
    let : MeasurableSpace (Cutoff.ShellSeq 2) := Cutoff.shellIndexSigma (Iic m)
    exact Measurable.tsum fun r => (measurable_shellFieldScalarRestriction K).comp
      (Cutoff.measurable_shellCoordinate_shellIndexSigma (by change m - (r : ℤ) ≤ m; omega))
  have hY : @Measurable _ _ (Cutoff.shellIndexSigma (Set.range k)) _ Y := by
    let : MeasurableSpace (Cutoff.ShellSeq 2) := Cutoff.shellIndexSigma (Set.range k)
    have hsh (i : Fin b) : Measurable (fun ω : Cutoff.ShellSeq 2 =>
        shellFieldScalarRestriction K (ω (k i))) :=
      (measurable_shellFieldScalarRestriction K).comp
        (Cutoff.measurable_shellCoordinate_shellIndexSigma (show k i ∈ Set.range k from ⟨i, rfl⟩))
    exact Finset.measurable_sum _ fun i _ => (hsh i).const_smul (c i)
  have hXb := hX.mono (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hYb := hY.mono (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hind := Cutoff.indepFun_of_measurable_shellIndexSigma_of_disjoint M
    (Set.disjoint_left.mpr (fun z hz hz' => by obtain ⟨i, rfl⟩ := hz'; exact (hk i).not_ge hz)) hX hY
  have hpair := hind.map_prod_eq_prod_map_map hXb.aemeasurable hYb.aemeasurable
  rw [← Cutoff.map_cutoffSampleLaw_val M,
    Measure.map_map (hXb.prodMk hYb) measurable_subtype_coe,
    Measure.map_map hXb measurable_subtype_coe,
    Measure.map_map hYb measurable_subtype_coe] at hpair
  exact (indepFun_iff_map_prod_eq_prod_map_map (measurable_olderField K ell m hK).aemeasurable
    (measurable_modelBandW K k c).aemeasurable).mpr hpair

/-- Exact independent-shell laws assemble into the direct-sum Hilbert series law, for the
weighted band; `hlaw` is the law of each weighted shell. -/
theorem modelBandW_law_of_factors {b : ℕ} [NeZero b]
    (V : Fin b → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, CompleteSpace (V i)] [∀ i, SecondCountableTopology (V i)]
    [∀ i, MeasurableSpace (V i)] [∀ i, BorelSpace (V i)]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2)
    (k : Fin b → ℤ) (c : Fin b → ℝ) (hk : Function.Injective k)
    (T : ∀ i, V i →L[ℝ] C(K, ℝ)) (v : ∀ i, ℕ → V i)
    (hv : ∀ i, Summable (fun j => ‖v i j‖ ^ 2))
    (hlaw : ∀ i, (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => c i • shellFieldScalarRestriction K (ω.1 (k i))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE (hv i) (T i))) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBandW K k c) =
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
  rw [hL, Measure.map_map L.continuous.measurable (measurable_modelBandW K k c),
    Measure.map_map L.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE hw A).measurable]
  have hi := (iIndepFun_shellRestrictions K M k hk).comp
    (fun i => fun f => L (c i • f))
    (fun i => L.continuous.measurable.comp (continuous_const_smul (c i)).measurable)
  let s : Fin b → ℝ≥0 := fun i => Real.toNNReal (∑' j, (L (T i (v i j))) ^ 2)
  have hs (i : Fin b) : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => L (c i • shellFieldScalarRestriction K (ω.1 (k i)))) = gaussianReal 0 (s i) := by
    have hm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        c i • shellFieldScalarRestriction K (ω.1 (k i))) :=
      ((measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (k i)).comp measurable_subtype_coe)).const_smul (c i)
    have hh := congrArg (fun ν : Measure C(K, ℝ) => ν.map L) (hlaw i)
    rw [Measure.map_map L.continuous.measurable hm,
      Measure.map_map L.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE (hv i) (T i)).measurable] at hh
    exact hh.trans (map_gaussianSeriesLimitE_linear (hv i) (T i) L)
  have hsum := independent_gaussian_sum_law (Cutoff.cutoffSampleLaw M).toMeasure
    (fun i ω => L (c i • shellFieldScalarRestriction K (ω.1 (k i)))) s
    (fun i => L.continuous.measurable.comp (((measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (k i)).comp measurable_subtype_coe)).const_smul (c i))) hi hs
  have he : (fun ω => L (modelBandW K k c ω)) =
      fun ω => ∑ i, L (c i • shellFieldScalarRestriction K (ω.1 (k i))) := by
    funext ω
    exact map_sum L _ _
  simp only [Function.comp_def]
  rw [he, hsum]
  have hseries := map_gaussianSeriesLimitE_linear hw A L
  rw [hseries]
  congr 2
  dsimp only [s, A, w]
  rw [finiteFactor_covariance V v hv T L, Real.toNNReal_sum_of_nonneg (fun i _ => tsum_nonneg fun j => sq_nonneg _)]

/-- The literal expectation after a finite fresh band, with separate old/fresh maps. -/
noncomputable def bandModelAverageW {b : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (m : ℤ) (k : Fin b → ℤ) (c : Fin b → ℝ)
    (A B : C(K, ℝ) →L[ℝ] E) (Φ : E → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, Φ (A (olderField K m ω) + Real.sqrt t • B (modelBandW K k c ω))
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- Exact product-law transfer for a physical finite band. -/
theorem bandModelAverage_eqW {b : ℕ} {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (c : Fin b → ℝ) (hk : ∀ i, m < k i)
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBandW K k c) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A B : C(K, ℝ) →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : Measurable Φ) (hg : HasPolynomialGrowth Φ) (t : ℝ) :
    bandModelAverageW K M m k c A B Φ t = randomBaseHeatAverage hA (B.comp T)
      (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map A) Φ t := by
  let ρ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := fun ω => A (olderField K m ω)
  let Y := fun ω => B (modelBandW K k c ω)
  have hX : Measurable X := A.continuous.measurable.comp (measurable_olderField K ell m hK)
  have hY : Measurable Y := B.continuous.measurable.comp (measurable_modelBandW K k c)
  have hi := (indepFun_olderField_bandW K M ell m hK k c hk).comp
    A.continuous.measurable B.continuous.measurable
  have hmap : ρ.map Y = standardGaussianInfinitePi.map (gaussianSeriesLimitE hA (B.comp T)) := by
    have hh := congrArg (fun ν : Measure C(K, ℝ) => ν.map B) hlaw
    rw [Measure.map_map B.continuous.measurable (measurable_modelBandW K k c),
      Measure.map_map B.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable] at hh
    exact hh
  have hMom : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) (ρ.map X) := by
    rw [show ρ.map X = ((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map A from
      (Measure.map_map A.continuous.measurable (measurable_olderField K ell m hK)).symm]
    exact polynomial_moments_map _ (integrable_polynomial_olderFieldLaw K M ell m hK) A
  have hh := (integral_independent_insertion ρ X Y hX hY hi hA (B.comp T) hmap hMom Φ hΦ hg t).2
  have hint := integrable_randomBaseHeatIntegrand hA (B.comp T) (ρ.map X) hMom Φ hΦ hg t
  have heq := hh.trans (integral_prod _ hint)
  simpa only [Measure.map_map A.continuous.measurable (measurable_olderField K ell m hK),
    X, Y, ρ, bandModelAverageW, randomBaseHeatAverage, gaussianSeriesHeatAverage,
    gaussianSeriesHeatArgument, Function.comp_def] using heq

/-- The heat identity for deterministic old/fresh images on the actual model law. -/
theorem c1On_bandModelAverageW {b : ℕ} {V F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (k : Fin b → ℤ) (c : Fin b → ℝ) (hk : ∀ i, m < k i)
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBandW K k c) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A B : C(K, ℝ) →L[ℝ] F) (Φ : F → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    ContinuousOn (bandModelAverageW K M m k c A B Φ) (Ici 0) ∧
    ContinuousOn (fun t => (1 / 2 : ℝ) * bandModelAverageW K M m k c A B
      (modelCovarianceTrace Φ (fun j => B (T (v j)))) t) (Ici 0) ∧
    (∀ t ∈ Ioi 0, HasDerivAt (bandModelAverageW K M m k c A B Φ)
      ((1 / 2 : ℝ) * bandModelAverageW K M m k c A B
        (modelCovarianceTrace Φ (fun j => B (T (v j)))) t) t) ∧
    HasDerivWithinAt (bandModelAverageW K M m k c A B Φ)
      ((1 / 2 : ℝ) * bandModelAverageW K M m k c A B
        (modelCovarianceTrace Φ (fun j => B (T (v j)))) 0) (Ici 0) 0 := by
  let ν := (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map A)
  have hm := polynomial_moments_map _ (integrable_polynomial_olderFieldLaw K M ell m hK) A
  have hg : HasPolynomialGrowth Φ := by
    obtain ⟨_, C, hC, d, hv, _, _⟩ := hΦ
    exact ⟨C, hC, d, hv⟩
  have heq : bandModelAverageW K M m k c A B Φ = randomBaseHeatAverage hA (B.comp T) ν Φ := by
    funext t
    exact bandModelAverage_eqW K M ell m hK k c hk hA T hlaw A B Φ hΦ.1.continuous.measurable hg t
  have htrace : bandModelAverageW K M m k c A B
      (modelCovarianceTrace Φ (fun j => B (T (v j)))) = randomBaseHeatTraceAverage hA (B.comp T) ν Φ := by
    funext t
    exact bandModelAverage_eqW K M ell m hK k c hk hA T hlaw A B _
      (measurable_modelCovarianceTrace Φ hΦ.1 _)
      (polynomial_modelCovarianceTrace _ (summable_sq_norm_gaussianDirections hA (B.comp T)) Φ hΦ) t
  rw [heq, htrace]
  exact c1On_randomBaseHeatAverage hA (B.comp T) ν hm Φ hΦ

/-- The fresh field has all finite moments on the actual completed law, by its exact law. -/
theorem memLp_band_of_lawW {b : ℕ}
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (k : Fin b → ℤ) (c : Fin b → ℝ)
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (modelBandW K k c) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    {p : ℝ} (hp : 2 ≤ p) :
    MemLp (modelBandW K k c)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi : MemLp (id : C(K, ℝ) → C(K, ℝ)) (ENNReal.ofReal p)
      (standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)) := by
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.aemeasurable).mpr
      (memLp_gaussianSeriesLimitE hA T hp)
  rw [← hlaw] at hi
  exact hi.comp_of_map (measurable_modelBandW K k c).aemeasurable

/-- Mapped model tests require no new moment hypothesis. -/
theorem memLp_bandModel_testW {b : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell)) (k : Fin b → ℤ) (c : Fin b → ℝ)
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (modelBandW K k c) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A B : C(K, ℝ) →L[ℝ] E) (Φ : E → ℝ) (hΦ : Measurable Φ) (hg : HasPolynomialGrowth Φ)
    (t : ℝ) {p : ℝ} (hp : 2 ≤ p) :
    MemLp (fun ω : Cutoff.CutoffSample 2 => Φ (A (olderField K m ω) +
      Real.sqrt t • B (modelBandW K k c ω)))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply memLp_polynomial _ _
    ((A.continuous.measurable.comp (measurable_olderField K ell m hK)).add
      ((B.continuous.measurable.comp (measurable_modelBandW K k c)).const_smul (Real.sqrt t)))
    (fun q hq => ((memLp_olderField K M ell m hK (by linarith : 1 ≤ q)).continuousLinearMap_comp A).add
      (((memLp_band_of_lawW K M k c hA T hlaw hq).continuousLinearMap_comp B).const_smul (Real.sqrt t)))
    Φ hΦ hg hp

/-- The law of a scaled shell is the series law with the scaled factor. -/
theorem map_shell_smul_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (s : ℤ)
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 s)) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)) (c : ℝ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => c • shellFieldScalarRestriction K (ω.1 s)) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA (c • T)) := by
  have hm : Measurable (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 s)) :=
    (measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply s).comp measurable_subtype_coe)
  have hc : Measurable (fun f : C(K, ℝ) => c • f) := (continuous_const_smul c).measurable
  have h1 : (fun ω : Cutoff.CutoffSample 2 => c • shellFieldScalarRestriction K (ω.1 s)) =
      (fun f : C(K, ℝ) => c • f) ∘ (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 s)) := rfl
  rw [h1, ← Measure.map_map hc hm, hlaw,
    Measure.map_map hc (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable]
  rfl

/-- Existence of the Hilbert-series realization of the weighted band. -/
theorem exists_modelBandW_realization {b : ℕ} [NeZero b]
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : Fin b → ℤ) (c : Fin b → ℝ) (hk : Function.Injective k) :
    ∃ (T : BandHilbert b →L[ℝ] C(K, ℝ))
      (v : ℕ → BandHilbert b) (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBandW K k c) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
  classical
  have hex (i : Fin b) := freshShell_map_scalarRestriction_eq_gaussianSeries M h hM (k i - 1) (K := K)
  choose T v hv hlaw using hex
  simp only [sub_add_cancel] at hlaw
  have hlawW (i : Fin b) := map_shell_smul_eq K M (k i) (hv i) (T i) (hlaw i) (c i)
  have hband := modelBandW_law_of_factors (fun _ : Fin b => GaussianFactorL2 ℕ) K M k c hk
    (fun i => c i • T i) v hv hlawW
  exact ⟨bandFactor (fun i => c i • T i), bandDirections v,
    bandDirections_summable v hv, hband⟩

/-- The second directional derivative is quadratic in the direction. -/
theorem secondDirectionalDerivative_smul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : E → ℝ) (x v : E) (c : ℝ) :
    secondDirectionalDerivative Φ x (c • v) = c ^ 2 * secondDirectionalDerivative Φ x v := by
  unfold secondDirectionalDerivative
  have h1 : (fun y => fderiv ℝ Φ y (c • v)) = c • (fun y => fderiv ℝ Φ y v) := by
    funext y
    simp [map_smul]
  rw [h1, fderiv_const_smul_field c]
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul]
  ring

theorem modelCovarianceTrace_smul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : E → ℝ) (H : ℕ → E) (c : ℝ) (x : E) :
    modelCovarianceTrace Φ (fun j => c • H j) x = c ^ 2 * modelCovarianceTrace Φ H x := by
  unfold modelCovarianceTrace
  simp_rw [secondDirectionalDerivative_smul']
  exact tsum_mul_left

end ASDExplicitGamma.Gaussian
