module

public import ASDExplicitGamma.Gaussian.AveragingBounds

/-! # The source auxiliary backward-heat test satisfies (8.8) -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The auxiliary backward heat test, in physical coefficient units. -/
noncomputable def backwardTest {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (S : V →L[ℝ] E)
    (Φ : E → ℝ) (θ t : ℝ) (x : E) : ℝ :=
  gaussianSeriesHeatAverage hA S Φ x ((1 + θ) * (1 - t))

/-- Its actual time derivative is the negative auxiliary covariance generator. -/
noncomputable def backwardTestDerivative {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (S : V →L[ℝ] E)
    (Φ : E → ℝ) (θ t : ℝ) (x : E) : ℝ :=
  -((1 + θ) / 2) * gaussianSeriesHeatTraceAverage hA S Φ x ((1 + θ) * (1 - t))

/-- All regularity and domination needed for the auxiliary backward test are proved from the
C² response bounds. In particular, no singular terminal-time derivative is assumed. -/
theorem backwardTest_regularity {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (S : V →L[ℝ] E)
    {Φ : E → ℝ} (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) {θ : ℝ} (hθ : 0 < θ) :
    TimeRegularity (backwardTest hA S Φ θ) (backwardTestDerivative hA S Φ θ) := by
  let Z := gaussianSeriesLimitE hA S
  let a : ℝ → ℝ := fun t => Real.sqrt ((1 + θ) * (1 - t))
  let R : ℝ := Real.sqrt (1 + θ)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have ha : Continuous a := Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have haR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |a t| ≤ R := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    nlinarith [ht.1, ht.2]
  have hZ : StronglyMeasurable Z := stronglyMeasurable_gaussianSeriesLimitE hA S
  have hMom (d : ℕ) : Integrable (fun ω => (1 + ‖Z ω‖) ^ d) standardGaussianInfinitePi := by
    have hz : MemLp Z ((d + 2 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi := by
      convert memLp_gaussianSeriesLimitE hA S (p := (d + 2 : ℕ))
        (by exact_mod_cast (show 2 ≤ d + 2 by omega)) using 1
      simp [ENNReal.ofReal_add]
    exact integrable_one_add_norm_pow_of_memLp hz
  have hscaled (t : ℝ) := c2_integral_translate standardGaussianInfinitePi
    (fun ω => a t • Z ω) (hZ.const_smul (a t))
    (integrable_scaled_moments standardGaussianInfinitePi Z hZ hMom (a t)) hΦ
  obtain ⟨C, hC, d, hb⟩ := polynomial_c2_jet_bound hΦ
  have hv (x : E) : ‖Φ x‖ ≤ C * (1 + ‖x‖) ^ d := by
    rw [Real.norm_eq_abs]
    have h := hb x
    linarith [norm_nonneg (fderiv ℝ Φ x), norm_nonneg (fderiv ℝ (fderiv ℝ Φ) x)]
  have hd (x : E) : ‖fderiv ℝ Φ x‖ ≤ C * (1 + ‖x‖) ^ d := by
    have h := hb x
    linarith [abs_nonneg (Φ x), norm_nonneg (fderiv ℝ (fderiv ℝ Φ) x)]
  have hh (x : E) : ‖fderiv ℝ (fderiv ℝ Φ) x‖ ≤ C * (1 + ‖x‖) ^ d := by
    have h := hb x
    linarith [abs_nonneg (Φ x), norm_nonneg (fderiv ℝ Φ x)]
  have hdf := hΦ.1.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hG0 : ContinuousOn (Function.uncurry (backwardTest hA S Φ θ)) (Icc (0 : ℝ) 1 ×ˢ univ) :=
    continuousOn_integral_scaled_translate standardGaussianInfinitePi Z hZ hMom
      hΦ.1.continuous ⟨C, hC, d, hv⟩ a ha R hR haR
  have hG1 : ContinuousOn (fun p : ℝ × E => fderiv ℝ (backwardTest hA S Φ θ p.1) p.2)
      (Icc (0 : ℝ) 1 ×ˢ univ) := by
    have hc := continuousOn_integral_scaled_translate standardGaussianInfinitePi Z hZ hMom
      hdf.continuous ⟨C, hC, d, hd⟩ a ha R hR haR
    apply hc.congr
    intro p hp
    exact (hscaled p.1).2.1 p.2
  have hG2 : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (backwardTest hA S Φ θ p.1)) p.2)
      (Icc (0 : ℝ) 1 ×ˢ univ) := by
    have hc := continuousOn_integral_scaled_translate standardGaussianInfinitePi Z hZ hMom
      (hdf.continuous_fderiv (by norm_num)) ⟨C, hC, d, hh⟩ a ha R hR haR
    apply hc.congr
    intro p hp
    exact (hscaled p.1).2.2 p.2
  let H : ℕ → E := fun j => S (v j)
  let Q : E → ℝ := modelCovarianceTrace Φ H
  have hH := summable_sq_norm_gaussianDirections hA S
  have hQcont : Continuous Q := continuous_modelCovarianceTrace hΦ H hH
  have hQpoly := polynomial_modelCovarianceTrace H hH Φ hΦ
  obtain ⟨CQ, hCQ, dQ, hQb⟩ := hQpoly
  have hDcont : ContinuousOn (Function.uncurry (backwardTestDerivative hA S Φ θ))
      (Icc (0 : ℝ) 1 ×ˢ univ) := by
    have hc := continuousOn_integral_scaled_translate standardGaussianInfinitePi Z hZ hMom
      hQcont ⟨CQ, hCQ, dQ, hQb⟩ a ha R hR haR
    exact continuousOn_const.mul hc
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
      HasDerivWithinAt (fun s => backwardTest hA S Φ θ s x)
        (backwardTestDerivative hA S Φ θ t x) (Icc 0 1) t := by
    let b : ℝ → ℝ := fun s => (1 + θ) * (1 - s)
    have hb0 : 0 ≤ b t := mul_nonneg (by linarith) (sub_nonneg.mpr ht.2)
    have hheat : HasDerivWithinAt (gaussianSeriesHeatAverage hA S Φ x)
        ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA S Φ x (b t)) (Ici 0) (b t) := by
      rcases hb0.eq_or_lt with hzero | hpos
      · rw [← hzero]
        exact hasDerivWithinAt_gaussianSeriesHeatAverage_zero hA S Φ hΦ x
      · exact (hasDerivAt_gaussianSeriesHeatAverage hA S Φ hΦ x hpos).hasDerivWithinAt
    have hbderiv : HasDerivWithinAt b (-(1 + θ)) (Icc 0 1) t := by
      have hd := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).const_mul (1 + θ)).hasDerivWithinAt (s := Icc 0 1)
      simpa only [b, Function.const_apply, Pi.sub_apply, id_eq, sub_self, zero_sub, mul_neg, mul_one] using hd
    have hmaps : MapsTo b (Icc 0 1) (Ici 0) := fun s hs => mul_nonneg (by linarith) (sub_nonneg.mpr hs.2)
    have h := hheat.comp t hbderiv hmaps
    convert h using 1 <;> dsimp [backwardTest, backwardTestDerivative, Function.comp_def, b]
    ring
  refine ⟨hG0, hDcont, fun t ht => (hscaled t).1, htime, hG1, hG2, ?_⟩
  let K : ℝ := C * (1 + R) ^ d * ∫ ω, (1 + ‖Z ω‖) ^ d ∂standardGaussianInfinitePi
  let J : ℝ := CQ * (1 + R) ^ dQ * ∫ ω, (1 + ‖Z ω‖) ^ dQ ∂standardGaussianInfinitePi
  have hK : 0 ≤ K := by dsimp [K]; exact mul_nonneg (by positivity) (integral_nonneg fun ω => pow_nonneg (by positivity) _)
  have hJ : 0 ≤ J := by dsimp [J]; exact mul_nonneg (by positivity) (integral_nonneg fun ω => pow_nonneg (by positivity) _)
  have hval (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
      |backwardTest hA S Φ θ t x| ≤ K * (1 + ‖x‖) ^ d :=
    norm_integral_scaled_translate_le standardGaussianInfinitePi Z (hMom d) hC hR hv (haR t ht) x
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
      ‖fderiv ℝ (backwardTest hA S Φ θ t) x‖ ≤ K * (1 + ‖x‖) ^ d := by
    change ‖fderiv ℝ (fun y => ∫ ω, Φ (y + a t • Z ω) ∂standardGaussianInfinitePi) x‖ ≤ _
    rw [(hscaled t).2.1 x]
    exact norm_integral_scaled_translate_le standardGaussianInfinitePi Z (hMom d) hC hR hd (haR t ht) x
  have hsecond (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
      ‖fderiv ℝ (fderiv ℝ (backwardTest hA S Φ θ t)) x‖ ≤ K * (1 + ‖x‖) ^ d := by
    change ‖fderiv ℝ (fderiv ℝ (fun y => ∫ ω, Φ (y + a t • Z ω) ∂standardGaussianInfinitePi)) x‖ ≤ _
    rw [(hscaled t).2.2 x]
    exact norm_integral_scaled_translate_le standardGaussianInfinitePi Z (hMom d) hC hR hh (haR t ht) x
  have htimebound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
      |backwardTestDerivative hA S Φ θ t x| ≤ ((1 + θ) / 2) * J * (1 + ‖x‖) ^ dQ := by
    have hnorm := norm_integral_scaled_translate_le standardGaussianInfinitePi Z (f := Q) (hMom dQ)
      hCQ hR (fun x => by simpa only [Real.norm_eq_abs] using hQb x) (haR t ht) x
    dsimp only [backwardTestDerivative]
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (1 + θ) / 2)]
    exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (by ring)
  refine ⟨3 * K + ((1 + θ) / 2) * J, by positivity, d + dQ, fun t ht x => ?_⟩
  have hp : (1 + ‖x‖) ^ d ≤ (1 + ‖x‖) ^ (d + dQ) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  have hpQ : (1 + ‖x‖) ^ dQ ≤ (1 + ‖x‖) ^ (d + dQ) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  have h1 := hval t ht x
  have h2 := hfirst t ht x
  have h3 := hsecond t ht x
  have h4 := htimebound t ht x
  have hm1 := mul_le_mul_of_nonneg_left hp hK
  have hm2 := mul_le_mul_of_nonneg_left hpQ (mul_nonneg (by positivity : 0 ≤ (1 + θ) / 2) hJ)
  nlinarith

end ASDExplicitGamma.Gaussian
