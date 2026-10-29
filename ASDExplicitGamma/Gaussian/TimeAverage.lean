module

public import ASDExplicitGamma.Gaussian.TimePath

/-! # The two-parameter Gaussian heat identity on an independent older/series product law -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Freezing time produces a valid time-independent test in the same source class. -/
theorem TimeRegularity.const_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G D : ℝ → E → ℝ} (hG : TimeRegularity G D) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    TimeRegularity (fun _ x => G s x) (fun _ _ => 0) := by
  have hf := hG.field_c2 s hs
  have hdf := hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  refine ⟨(hf.continuous.comp continuous_snd).continuousOn, continuousOn_const,
    (fun _ _ => hf), (fun t _ x => hasDerivWithinAt_const t _ _),
    (hdf.continuous.comp continuous_snd).continuousOn,
    ((hdf.continuous_fderiv (by norm_num)).comp continuous_snd).continuousOn, ?_⟩
  obtain ⟨C, hC, d, hb⟩ := hG.polynomial_bound
  refine ⟨C, hC, d, fun t ht x => ?_⟩
  have h := hb s hs x
  simp only [abs_zero, add_zero]
  linarith [abs_nonneg (D s x)]

section
variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
  (ν : Measure E) [IsFiniteMeasure ν]

omit [SecondCountableTopology E] [IsFiniteMeasure ν] in
/-- The common polynomial envelope on the independent older/series probability space. -/
theorem integrable_product_envelope
    (hν : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) ν) (d : ℕ) :
    Integrable (fun p : E × (ℕ → ℝ) =>
      (1 + ‖p.1‖ + ‖gaussianSeriesLimitE hA T p.2‖) ^ d)
      (ν.prod standardGaussianInfinitePi) := by
  have hz : MemLp (gaussianSeriesLimitE hA T) ((d + 2 : ℕ) : ℝ≥0∞)
      standardGaussianInfinitePi := by
    convert memLp_gaussianSeriesLimitE hA T (p := (d + 2 : ℕ))
      (by exact_mod_cast (show 2 ≤ d + 2 by omega)) using 1
    simp [ENNReal.ofReal_add]
  have hi := (hν d).mul_prod (integrable_one_add_norm_pow_of_memLp hz)
  have hm : Measurable (fun p : E × (ℕ → ℝ) =>
      (1 + ‖p.1‖ + ‖gaussianSeriesLimitE hA T p.2‖) ^ d) := by
    exact ((measurable_const.add measurable_fst.norm).add
      ((stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.comp measurable_snd).norm).pow_const d
  apply hi.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    have hb : 1 + ‖p.1‖ + ‖gaussianSeriesLimitE hA T p.2‖ ≤
        (1 + ‖p.1‖) * (1 + ‖gaussianSeriesLimitE hA T p.2‖) := by
      nlinarith [mul_nonneg (norm_nonneg p.1) (norm_nonneg (gaussianSeriesLimitE hA T p.2))]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (1 + ‖p.1‖ + ‖gaussianSeriesLimitE hA T p.2‖) ^ d), mul_pow] using
      pow_le_pow_left₀ (by positivity) hb d

/-- The expectation (8.9), before any stationarity comparison. -/
noncomputable def timeHeatAverage (G : ℝ → E → ℝ) (t : ℝ) : ℝ :=
  ∫ p : E × (ℕ → ℝ), G t (p.1 + Real.sqrt t • gaussianSeriesLimitE hA T p.2)
    ∂ν.prod standardGaussianInfinitePi

/-- The displayed expected time derivative plus the full covariance generator. -/
noncomputable def timeHeatDerivative (G D : ℝ → E → ℝ) (t : ℝ) : ℝ :=
  (∫ p : E × (ℕ → ℝ), D t (p.1 + Real.sqrt t • gaussianSeriesLimitE hA T p.2)
    ∂ν.prod standardGaussianInfinitePi) +
      (1 / 2 : ℝ) * randomBaseHeatTraceAverage hA T ν (G t) t

/-- The positive-time two-parameter identity follows from the chain rule and the already
proved fixed-time Gaussian heat identity; this retains all covariance directions. -/
theorem hasDerivAt_timeHeatAverage
    (hν : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) ν)
    {G D : ℝ → E → ℝ} (hG : TimeRegularity G D)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (timeHeatAverage hA T ν G) (timeHeatDerivative hA T ν G D t) t := by
  let μ := ν.prod standardGaussianInfinitePi
  let X : E × (ℕ → ℝ) → E := Prod.fst
  let Z : E × (ℕ → ℝ) → E := fun p => gaussianSeriesLimitE hA T p.2
  have hX : Measurable X := measurable_fst
  have hZ : Measurable Z := (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.comp measurable_snd
  have hm := integrable_product_envelope hA T ν hν
  have hfull := hG.hasDerivAt_integral_path μ X Z hX hZ hm ht
  have hfixed := (hG.const_slice ⟨ht.1.le, ht.2.le⟩).hasDerivAt_integral_path μ X Z hX hZ hm ht
  have hpoly : HasPolynomialGrowth (G t) := by
    obtain ⟨_, C, hC, d, hv, _, _⟩ := hG.field_growth ⟨ht.1.le, ht.2.le⟩
    exact ⟨C, hC, d, hv⟩
  have heq : (fun s => ∫ p, G t (X p + Real.sqrt s • Z p) ∂μ) =
      randomBaseHeatAverage hA T ν (G t) := by
    funext s
    exact integral_prod _ (integrable_randomBaseHeatIntegrand hA T ν hν (G t)
      (hG.field_c2 t ⟨ht.1.le, ht.2.le⟩).continuous.measurable hpoly s)
  have hheat := (c1On_randomBaseHeatAverage hA T ν hν (G t)
    (hG.field_growth ⟨ht.1.le, ht.2.le⟩)).2.2.1 t ht.1
  rw [← heq] at hheat
  have hrad : (∫ p, timePathDerivative (fun _ x => G t x) (fun _ _ => 0) (X p) (Z p) t ∂μ) =
      (1 / 2 : ℝ) * randomBaseHeatTraceAverage hA T ν (G t) t := hfixed.2.unique hheat
  have hDint : Integrable (fun p => D t (X p + Real.sqrt t • Z p)) μ := by
    convert hfull.1.sub hfixed.1 using 1
    ext p
    simp only [timePathDerivative, zero_add, Pi.sub_apply, add_sub_cancel_right]
  have hsplit : (fun p => timePathDerivative G D (X p) (Z p) t) =
      (fun p => D t (X p + Real.sqrt t • Z p) +
        timePathDerivative (fun _ x => G t x) (fun _ _ => 0) (X p) (Z p) t) := by
    funext p
    simp only [timePathDerivative, zero_add]
  have hderiv := hfull.2
  rw [hsplit] at hderiv
  rw [integral_add hDint hfixed.1, hrad] at hderiv
  exact hderiv

end
end ASDExplicitGamma.Gaussian
