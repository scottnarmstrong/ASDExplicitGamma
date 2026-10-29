module

public import ASDExplicitGamma.Gaussian.SeriesPower
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Averaging the Gaussian heat identity over a random older coefficient -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
private theorem heat_argument_bound (x z : E) {s R : ℝ} (hs : s ≤ R) :
    1 + ‖x + Real.sqrt s • z‖ ≤ (1 + ‖x‖) * (1 + Real.sqrt R * ‖z‖) := by
  have htri := norm_add_le x (Real.sqrt s • z)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)] at htri
  have hm := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hs) (norm_nonneg z)
  have hp : 0 ≤ ‖x‖ * (Real.sqrt R * ‖z‖) := by positivity
  nlinarith

private theorem measurable_heatAverage (Φ : E → ℝ) (hΦ : Continuous Φ) (s : ℝ) :
    Measurable (fun x => gaussianSeriesHeatAverage hA T Φ x s) := by
  have hm : Measurable (fun p : E × (ℕ → ℝ) =>
      Φ (p.1 + Real.sqrt s • gaussianSeriesLimitE hA T p.2)) :=
    hΦ.measurable.comp (measurable_fst.add
      (((stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.comp measurable_snd).const_smul _))
  exact hm.stronglyMeasurable.integral_prod_right.measurable

private theorem measurable_heatTraceAverage (Φ : E → ℝ) (hΦ : ContDiff ℝ 2 Φ) (s : ℝ) :
    Measurable (fun x => gaussianSeriesHeatTraceAverage hA T Φ x s) := by
  have hm : Measurable (fun p : E × (ℕ → ℝ) =>
      ∑' j, secondDirectionalDerivative Φ
        (p.1 + Real.sqrt s • gaussianSeriesLimitE hA T p.2) (T (v j))) := by
    apply Measurable.tsum
    intro j
    exact (continuous_secondDirectionalDerivative hΦ (T (v j))).measurable.comp
      (measurable_fst.add
        (((stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.comp measurable_snd).const_smul _))
  exact hm.stronglyMeasurable.integral_prod_right.measurable

omit [SecondCountableTopology E] in
/-- Both the heat average and its covariance trace have polynomial bounds in the older
coefficient, locally uniform in time. -/
theorem gaussianSeriesHeatAverage_trace_polynomial_bound
    (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ x s, s ≤ R →
      ‖gaussianSeriesHeatAverage hA T Φ x s‖ ≤ C * (1 + ‖x‖) ^ d ∧
      ‖gaussianSeriesHeatTraceAverage hA T Φ x s‖ ≤ C * (1 + ‖x‖) ^ d := by
  obtain ⟨hC2, C, hC, d, hval, hfirst, hsecond⟩ := hΦ
  let B : ℝ := 1 + Real.sqrt R * ‖T‖
  let P : (ℕ → ℝ) → ℝ := fun ω => (1 + gaussianFastEnvelope hA ω) ^ d
  let S : ℝ := ∑' j, ‖T (v j)‖ ^ 2
  let A : ℝ := C * B ^ d * ∫ ω, P ω ∂standardGaussianInfinitePi
  have hPint : Integrable P standardGaussianInfinitePi := integrable_fastEnvelope_polynomial hA d
  have hS : 0 ≤ S := tsum_nonneg fun _ => sq_nonneg _
  have hP : ∀ ω, 0 ≤ P ω := fun ω => by
    dsimp [P]
    exact pow_nonneg (by linarith [(show 0 ≤ gaussianFastEnvelope hA ω from by
      unfold gaussianFastEnvelope gaussianFastVariation
      exact add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _))]) _
  have hA0 : 0 ≤ A := mul_nonneg (by dsimp [B]; positivity) (integral_nonneg hP)
  refine ⟨A * (1 + S), mul_nonneg hA0 (by positivity), d, ?_⟩
  intro x s hs
  have harg : ∀ᵐ ω ∂standardGaussianInfinitePi,
      (1 + ‖gaussianSeriesHeatArgument hA T x s ω‖) ^ d ≤
        (1 + ‖x‖) ^ d * B ^ d * P ω := by
    filter_upwards [ae_norm_gaussianSeriesLimit_le_fastEnvelope hA] with ω hω
    have hZ : ‖gaussianSeriesLimitE hA T ω‖ ≤ ‖T‖ * gaussianFastEnvelope hA ω :=
      (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hω (norm_nonneg _))
    have hb : 1 + Real.sqrt R * ‖gaussianSeriesLimitE hA T ω‖ ≤
        B * (1 + gaussianFastEnvelope hA ω) := by
      have henv := (show 0 ≤ gaussianFastEnvelope hA ω from by
      unfold gaussianFastEnvelope gaussianFastVariation
      exact add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _))
      have hmul := mul_le_mul_of_nonneg_left hZ (Real.sqrt_nonneg R)
      dsimp [B]
      nlinarith [mul_nonneg (Real.sqrt_nonneg R) (norm_nonneg T)]
    have hy := (heat_argument_bound x (gaussianSeriesLimitE hA T ω) hs).trans
      (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1 + ‖x‖))
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x + Real.sqrt s • gaussianSeriesLimitE hA T ω‖) hy d
    simpa only [gaussianSeriesHeatArgument, mul_pow, mul_assoc, P] using hh
  have havg : ‖gaussianSeriesHeatAverage hA T Φ x s‖ ≤ A * (1 + ‖x‖) ^ d := by
    have hb : ∀ᵐ ω ∂standardGaussianInfinitePi,
        ‖Φ (gaussianSeriesHeatArgument hA T x s ω)‖ ≤
          (C * (1 + ‖x‖) ^ d * B ^ d) * P ω := by
      filter_upwards [harg] with ω hω
      rw [Real.norm_eq_abs]
      exact (hval _).trans (by nlinarith [mul_le_mul_of_nonneg_left hω hC])
    have hi := norm_integral_le_of_norm_le
      (hPint.const_mul (C * (1 + ‖x‖) ^ d * B ^ d)) hb
    simpa only [gaussianSeriesHeatAverage, integral_const_mul, A, mul_assoc, mul_left_comm,
      mul_comm] using hi
  have htrace : ‖gaussianSeriesHeatTraceAverage hA T Φ x s‖ ≤ A * S * (1 + ‖x‖) ^ d := by
    have hGrowth : HasPolynomiallyBoundedSecondDirectionalDerivative Φ :=
      ⟨C, hC, d, fun y w => by
        simpa only [secondDirectionalDerivative, pow_two, ← mul_assoc] using hsecond y w w⟩
    have hb : ∀ᵐ ω ∂standardGaussianInfinitePi,
        ‖gaussianSeriesHeatTrace hA T Φ x s ω‖ ≤
          (C * (1 + ‖x‖) ^ d * B ^ d * S) * P ω := by
      filter_upwards [harg] with ω hω
      have hsum := summable_gaussianSeriesHeatTrace hA T Φ hGrowth x s ω
      have hdir := summable_sq_norm_gaussianDirections hA T
      have hterm : ∀ j, ‖secondDirectionalDerivative Φ
          (gaussianSeriesHeatArgument hA T x s ω) (T (v j))‖ ≤
          (C * (1 + ‖gaussianSeriesHeatArgument hA T x s ω‖) ^ d) * ‖T (v j)‖ ^ 2 := by
        intro j
        rw [Real.norm_eq_abs]
        simpa only [secondDirectionalDerivative, pow_two, ← mul_assoc] using
          hsecond (gaussianSeriesHeatArgument hA T x s ω) (T (v j)) (T (v j))
      have ht := norm_tsum_le_tsum_norm hsum.norm
      have hle := hsum.norm.tsum_le_tsum hterm
        (hdir.mul_left (C * (1 + ‖gaussianSeriesHeatArgument hA T x s ω‖) ^ d))
      rw [tsum_mul_left] at hle
      have hf := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hω hC) hS
      change ‖∑' j, secondDirectionalDerivative Φ
        (gaussianSeriesHeatArgument hA T x s ω) (T (v j))‖ ≤ _
      calc
        _ ≤ C * (1 + ‖gaussianSeriesHeatArgument hA T x s ω‖) ^ d * S := ht.trans hle
        _ ≤ _ := by nlinarith [hf]
    have hi := norm_integral_le_of_norm_le
      (hPint.const_mul (C * (1 + ‖x‖) ^ d * B ^ d * S)) hb
    simpa only [gaussianSeriesHeatTraceAverage, integral_const_mul, integral_mul_const, A, mul_assoc,
      mul_left_comm, mul_comm] using hi
  constructor
  · exact havg.trans (by nlinarith [mul_nonneg hA0 (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) d)])
  · exact htrace.trans (by nlinarith [mul_nonneg hA0 (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) d)])

/-- The absolutely convergent Hessian trace in the physical coefficient directions. -/
noncomputable def modelCovarianceTrace (Φ : E → ℝ) (H : ℕ → E) (x : E) : ℝ :=
  ∑' j, secondDirectionalDerivative Φ x (H j)

omit [SecondCountableTopology E] in
theorem measurable_modelCovarianceTrace (Φ : E → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (H : ℕ → E) : Measurable (modelCovarianceTrace Φ H) := by
  exact Measurable.tsum fun j => (continuous_secondDirectionalDerivative hΦ (H j)).measurable

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem polynomial_modelCovarianceTrace (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2)) (Φ : E → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    HasPolynomialGrowth (modelCovarianceTrace Φ H) := by
  obtain ⟨C, hC, d, hsecond⟩ :=
    hasPolynomiallyBoundedSecondDirectionalDerivative_of_C2Derivatives hΦ
  let S := ∑' j, ‖H j‖ ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun j => sq_nonneg _
  refine ⟨C * S, mul_nonneg hC hS, d, ?_⟩
  intro x
  have hdir := hH
  have hb (j : ℕ) : ‖secondDirectionalDerivative Φ x (H j)‖ ≤
      (C * (1 + ‖x‖) ^ d) * ‖H j‖ ^ 2 := hsecond x (H j)
  have hs := (hdir.mul_left (C * (1 + ‖x‖) ^ d)).of_norm_bounded hb
  have hle := (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum hb (hdir.mul_left (C * (1 + ‖x‖) ^ d)))
  rw [tsum_mul_left] at hle
  simpa only [modelCovarianceTrace, Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using hle

/-- Polynomial observables are integrable under the independent older/series product law. -/
theorem integrable_randomBaseHeatIntegrand (μ : Measure E) [IsFiniteMeasure μ]
    (hμ : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) μ)
    (Ψ : E → ℝ) (hΨ : Measurable Ψ) (hg : HasPolynomialGrowth Ψ) (t : ℝ) :
    Integrable (fun p : E × (ℕ → ℝ) =>
      Ψ (p.1 + Real.sqrt t • gaussianSeriesLimitE hA T p.2))
      (μ.prod standardGaussianInfinitePi) := by
  obtain ⟨C, hC, d, hb⟩ := hg
  have hZ : MemLp (gaussianSeriesLimitE hA T) ((d + 2 : ℕ) : ℝ≥0∞)
      standardGaussianInfinitePi := by
    convert memLp_gaussianSeriesLimitE hA T (p := (d + 2 : ℕ))
      (by exact_mod_cast (show 2 ≤ d + 2 by omega)) using 1
    simp [ENNReal.ofReal_add]
  have hZi := integrable_one_add_norm_pow_of_memLp hZ
  have hi := ((hμ d).mul_prod hZi).const_mul (C * (1 + Real.sqrt t) ^ d)
  have hm : Measurable (fun p : E × (ℕ → ℝ) =>
      Ψ (p.1 + Real.sqrt t • gaussianSeriesLimitE hA T p.2)) :=
    hΨ.comp (measurable_fst.add
      (((stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.comp measurable_snd).const_smul _))
  apply hi.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    have harg := heat_argument_bound p.1 (gaussianSeriesLimitE hA T p.2) (le_refl t)
    have hz : 1 + Real.sqrt t * ‖gaussianSeriesLimitE hA T p.2‖ ≤
        (1 + Real.sqrt t) * (1 + ‖gaussianSeriesLimitE hA T p.2‖) := by
      nlinarith [Real.sqrt_nonneg t, norm_nonneg (gaussianSeriesLimitE hA T p.2)]
    have harg' := harg.trans (mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 1 + ‖p.1‖))
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) harg' d) hC
    rw [Real.norm_eq_abs]
    exact (hb _).trans (by simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hp)

/-- Average over both an older coefficient law and the independent fresh Gaussian series. -/
noncomputable def randomBaseHeatAverage (μ : Measure E) (Φ : E → ℝ) (t : ℝ) : ℝ :=
  ∫ x, gaussianSeriesHeatAverage hA T Φ x t ∂μ

/-- The expected covariance trace over the same product law. -/
noncomputable def randomBaseHeatTraceAverage (μ : Measure E) (Φ : E → ℝ) (t : ℝ) : ℝ :=
  ∫ x, gaussianSeriesHeatTraceAverage hA T Φ x t ∂μ

/-- Conditioning on an independent older coefficient preserves the Gaussian heat identity.
All polynomial moments of the older law suffice; no derivative or heat identity is assumed
for that law. -/
theorem c1On_randomBaseHeatAverage (μ : Measure E) [IsFiniteMeasure μ]
    (hμ : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) μ)
    (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    ContinuousOn (randomBaseHeatAverage hA T μ Φ) (Ici 0) ∧
    ContinuousOn (fun t => (1 / 2 : ℝ) * randomBaseHeatTraceAverage hA T μ Φ t) (Ici 0) ∧
    (∀ t ∈ Ioi 0, HasDerivAt (randomBaseHeatAverage hA T μ Φ)
      ((1 / 2 : ℝ) * randomBaseHeatTraceAverage hA T μ Φ t) t) ∧
    HasDerivWithinAt (randomBaseHeatAverage hA T μ Φ)
      ((1 / 2 : ℝ) * randomBaseHeatTraceAverage hA T μ Φ 0) (Ici 0) 0 := by
  let F : ℝ → E → ℝ := fun t x => gaussianSeriesHeatAverage hA T Φ x t
  let D : ℝ → E → ℝ := fun t x => (1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA T Φ x t
  have hFmeas (t : ℝ) : Measurable (F t) := measurable_heatAverage hA T Φ hΦ.1.continuous t
  have hDmeas (t : ℝ) : Measurable (D t) :=
    measurable_const.mul (measurable_heatTraceAverage hA T Φ hΦ.1 t)
  have hbound (R : ℝ) : ∃ b : E → ℝ, Integrable b μ ∧
      ∀ s, s ≤ R → ∀ x, ‖F s x‖ ≤ b x ∧ ‖D s x‖ ≤ b x := by
    obtain ⟨C, hC, d, hb⟩ := gaussianSeriesHeatAverage_trace_polynomial_bound hA T Φ hΦ R
    refine ⟨fun x => C * (1 + ‖x‖) ^ d, (hμ d).const_mul C, ?_⟩
    intro s hs x
    refine ⟨(hb x s hs).1, ?_⟩
    dsimp [D]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans (hb x s hs).2
  have hcontF : ContinuousOn (fun t => ∫ x, F t x ∂μ) (Ici 0) := by
    intro t ht
    obtain ⟨b, hb, hbound⟩ := hbound (t + 1)
    apply continuousWithinAt_of_dominated
      (Eventually.of_forall fun s => (hFmeas s).aestronglyMeasurable)
      (bound := b) ?_ hb
    · exact Eventually.of_forall fun x => (c1On_gaussianSeriesHeatAverage hA T Φ hΦ x).1 t ht
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t < t + 1 by linarith))] with s hs
      exact Eventually.of_forall fun x => (hbound s hs.le x).1
  have hcontD : ContinuousOn (fun t => ∫ x, D t x ∂μ) (Ici 0) := by
    intro t ht
    obtain ⟨b, hb, hbound⟩ := hbound (t + 1)
    apply continuousWithinAt_of_dominated
      (Eventually.of_forall fun s => (hDmeas s).aestronglyMeasurable)
      (bound := b) ?_ hb
    · exact Eventually.of_forall fun x => (c1On_gaussianSeriesHeatAverage hA T Φ hΦ x).2.1 t ht
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t < t + 1 by linarith))] with s hs
      exact Eventually.of_forall fun x => (hbound s hs.le x).2
  have hdiff : ∀ t ∈ Ioi 0, HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, D t x ∂μ) t := by
    intro t ht
    obtain ⟨b, hb, hbound⟩ := hbound (t + 1)
    have hint : Integrable (F t) μ := hb.mono' (hFmeas t).aestronglyMeasurable
      (Eventually.of_forall fun x => (hbound t (by linarith) x).1)
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := D) (bound := b)
      (Ioo_mem_nhds ht (show t < t + 1 by linarith))
      (Eventually.of_forall fun s => (hFmeas s).aestronglyMeasurable)
      hint (hDmeas t).aestronglyMeasurable ?_ hb ?_).2
    · exact Eventually.of_forall fun x s hs => (hbound s hs.2.le x).2
    · exact Eventually.of_forall fun x s hs =>
        (c1On_gaussianSeriesHeatAverage hA T Φ hΦ x).2.2.1 s hs.1
  have hzero : HasDerivWithinAt (fun s => ∫ x, F s x ∂μ)
      (∫ x, D 0 x ∂μ) (Ici 0) 0 := by
    have hlim : Tendsto (fun t => deriv (fun s => ∫ x, F s x ∂μ) t)
        (𝓝[>] 0) (𝓝 (∫ x, D 0 x ∂μ)) := by
      have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ),
          deriv (fun s => ∫ x, F s x ∂μ) t = ∫ x, D t x ∂μ := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact (hdiff t ht).deriv
      exact ((hcontD 0 (by simp)).mono Ioi_subset_Ici_self).congr' (heq.mono fun _ h => h.symm)
    exact hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hdiff t ht).differentiableAt.differentiableWithinAt)
      ((hcontF 0 (by simp)).mono Ioi_subset_Ici_self)
      self_mem_nhdsWithin hlim
  dsimp only [randomBaseHeatAverage, randomBaseHeatTraceAverage]
  refine ⟨hcontF, ?_, ?_, ?_⟩
  · simpa only [D, integral_const_mul] using hcontD
  · intro t ht
    unfold randomBaseHeatAverage
    simpa only [F, D, integral_const_mul] using hdiff t ht
  · unfold randomBaseHeatAverage
    simpa only [F, D, integral_const_mul] using hzero

end
end ASDExplicitGamma.Gaussian
