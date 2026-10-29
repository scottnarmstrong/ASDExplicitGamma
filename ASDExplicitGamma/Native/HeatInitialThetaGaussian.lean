module

public import ASDExplicitGamma.Native.HeatStepThetaRow
public import ASDExplicitGamma.Native.HeatInitialRefinedGaussianGen

/-! Theta-scaled Gaussian moments of the depth-ten centre quadratic of the refined heat carrier:
the `r`-th moment is at most `θ^r` times the configured Gaussian row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal

theorem nativeHeat_scaledVariance_capTheta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (hgamma : M.gamma ≤ gammaZero) :
    (ns : ℝ) * ((1 + (nativeHeatTheta : ℝ)) *
        ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)))) ≤
      theta M * ((nativeHeatGenVariance ns) : ℝ) := by
  have hfactor : (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)) ≤
      theta M * ((nativeHeatOldRowGen ns).e : ℝ) :=
    (nativeHeatStep_driftTheta ns M hnum hgamma).1.2
  obtain ⟨hθ0, _⟩ := theta_pos_le_one M hgamma
  have hdataQ : (1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ) ≤
      (nativeHeatGenVariance ns) := by
    rw [nativeHeatGenVariance_eq]
    exact nativeUp_ge _
  have hdata : (1 + (nativeHeatTheta : ℝ)) * (ns : ℝ) * ((nativeHeatOldRowGen ns).e : ℝ) ≤
        ((nativeHeatGenVariance ns) : ℝ) := by
    have hdataCast :
        (((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ) : ℚ) : ℝ) ≤
          ((nativeHeatGenVariance ns) : ℝ) := by exact_mod_cast hdataQ
    calc _ = (((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ) : ℚ) : ℝ) := by
          simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_natCast]; ring
      _ ≤ _ := hdataCast
  have hscale0 : 0 ≤ (1 + (nativeHeatTheta : ℝ)) := by norm_num [nativeHeatTheta]
  calc _ = (ns : ℝ) * (1 + (nativeHeatTheta : ℝ)) *
        ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))) := by ring
    _ ≤ (ns : ℝ) * (1 + (nativeHeatTheta : ℝ)) * (theta M * ((nativeHeatOldRowGen ns).e : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (mul_nonneg (by positivity) hscale0)
    _ = theta M * ((1 + (nativeHeatTheta : ℝ)) * (ns : ℝ) * ((nativeHeatOldRowGen ns).e : ℝ)) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdata hθ0.le

theorem nativeHeat_scaledSpectral_capTheta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (hgamma : M.gamma ≤ gammaZero) :
    ((1 + (nativeHeatTheta : ℝ)) *
      ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)))) *
      min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) ≤
        theta M * ((nativeHeatGenSpectral ns) : ℝ) := by
  have hfactor : (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)) ≤
      theta M * ((nativeHeatOldRowGen ns).e : ℝ) :=
    (nativeHeatStep_driftTheta ns M hnum hgamma).1.2
  obtain ⟨hθ0, _⟩ := theta_pos_le_one M hgamma
  have hdataQ : (1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e *
        min (ns : ℚ) (((max (ns - 8) 0 : ℕ) : ℚ) + 25 / 72) ≤
      (nativeHeatGenSpectral ns) := by
    rw [nativeHeatGenSpectral_eq]
    exact nativeUp_ge _
  have hdata : (1 + (nativeHeatTheta : ℝ)) * ((nativeHeatOldRowGen ns).e : ℝ) *
        min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) ≤
        ((nativeHeatGenSpectral ns) : ℝ) := by
    have hdataCast :
        (((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e *
          min (ns : ℚ) (((max (ns - 8) 0 : ℕ) : ℚ) + 25 / 72) : ℚ) : ℝ) ≤
        ((nativeHeatGenSpectral ns) : ℝ) := by exact_mod_cast hdataQ
    calc _ = (((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e *
          min (ns : ℚ) (((max (ns - 8) 0 : ℕ) : ℚ) + 25 / 72) : ℚ) : ℝ) := by
          push_cast; ring
      _ ≤ _ := hdataCast
  have hscale0 : 0 ≤ (1 + (nativeHeatTheta : ℝ)) := by norm_num [nativeHeatTheta]
  have hL : 0 ≤ min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) := by positivity
  calc _ = (1 + (nativeHeatTheta : ℝ)) *
        min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) *
        ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))) := by ring
    _ ≤ (1 + (nativeHeatTheta : ℝ)) *
        min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72) *
        (theta M * ((nativeHeatOldRowGen ns).e : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (mul_nonneg hscale0 hL)
    _ = theta M * ((1 + (nativeHeatTheta : ℝ)) * ((nativeHeatOldRowGen ns).e : ℝ) *
        min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdata hθ0.le

theorem nativeHeatRefined_gridMoment_le_theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (hgamma : M.gamma ≤ gammaZero) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r ≤ 20) :
    ∫ ω, nativeHeatRefinedGridQuadraticGen ns M n ω ^ r
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        theta M ^ r * (((nativeHeatGenQm ns).getD r 0 : ℚ) : ℝ) := by
  have hscale : 0 ≤ (1 + (nativeHeatTheta : ℝ)) := by norm_num [nativeHeatTheta]
  have hprod := nativeHeatRefined_gridMoment_product_of_stateGen ns M h hM n
    (1 + (nativeHeatTheta : ℝ)) hscale r hstate
  dsimp only at hprod
  obtain ⟨hθ0, _⟩ := theta_pos_le_one M hgamma
  have hV : 0 ≤ ((nativeHeatGenVariance ns) : ℚ) := hnum.variance_nonneg
  have hS : 0 ≤ ((nativeHeatGenSpectral ns) : ℚ) := hnum.spectral_nonneg
  have hvar := nativeHeat_scaledVariance_capTheta ns hnum M hgamma
  have hspec := nativeHeat_scaledSpectral_capTheta ns hnum M hgamma
  have htable := nativeGaussianMoments_product_le (nativeHeatGenVariance ns)
    (nativeHeatGenSpectral ns) hV hS r hr
  rw [← nativeHeatGenQm_eq] at htable
  have htableR : ∏ i ∈ Finset.range r, (((nativeHeatGenVariance ns) : ℝ) +
      2 * (i : ℝ) * ((nativeHeatGenSpectral ns) : ℝ)) ≤
        (((nativeHeatGenQm ns).getD r 0 : ℚ) : ℝ) := by exact_mod_cast htable
  have hprod2 : ∏ i ∈ Finset.range r,
      ((ns : ℝ) * ((1 + (nativeHeatTheta : ℝ)) *
          ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)))) +
        2 * (i : ℝ) * ((1 + (nativeHeatTheta : ℝ)) *
          ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)))) *
          min (ns : ℝ) (((max (ns - 8) 0 : ℕ) : ℝ) + 25 / 72)) ≤
      ∏ i ∈ Finset.range r, (theta M * (((nativeHeatGenVariance ns) : ℝ) +
        2 * (i : ℝ) * ((nativeHeatGenSpectral ns) : ℝ))) := by
    apply Finset.prod_le_prod₀
    · intro i _
      have : 0 ≤ (1 + (nativeHeatTheta : ℝ)) *
          ((9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))) := by
        have := M.shellPrefix.gamma_pos.le
        positivity
      positivity
    · intro i _
      have hi : (0 : ℝ) ≤ 2 * (i : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hspec hi
      nlinarith [hvar, this]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hprod2
  have hmoment := hprod.trans (hprod2.trans
    (mul_le_mul_of_nonneg_left htableR (pow_nonneg hθ0.le r)))
  refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans_le hmoment
  simp only [nativeHeatRefinedGridQuadraticGen, mul_assoc]

theorem nativeHeatRefined_gridMoment_lintegral_le_theta (ns : ℕ) [NeZero ns]
    (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (hgamma : M.gamma ≤ gammaZero) (hstate : nativeInductionState M h n)
    (j : ℕ) (hj20 : j ≤ 20) :
    ∫⁻ ω, ENNReal.ofReal (nativeHeatRefinedGridQuadraticGen ns M n ω ^ j)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)) := by
  letI : IsProbabilityMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    (Cutoff.cutoffSampleLaw M).property
  have hfin := nativeHeatRefined_gridMoment_lintegral_le_009_of_stateGen ns hnum M h hM n hgamma
    hstate j hj20
  have hFnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ nativeHeatRefinedGridQuadraticGen ns M n ω :=
    nativeHeatRefined_gridQuadratic_nonnegGen ns M n ω
  have hmeas : Measurable (fun ω => nativeHeatRefinedGridQuadraticGen ns M n ω ^ j) :=
    (nativeHeatRefined_gridQuadratic_measurableGen ns M n).pow_const j
  have hInt : Integrable (fun ω => nativeHeatRefinedGridQuadraticGen ns M n ω ^ j)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hFnonneg ω) j)).mp
      (ne_of_lt (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top))
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun ω => pow_nonneg (hFnonneg ω) j)]
  exact ENNReal.ofReal_le_ofReal
    (nativeHeatRefined_gridMoment_le_theta ns hnum M h hM n hgamma hstate j hj20)

/-- The depth-ten source centre quadratic, theta-scaled Gaussian row. -/
theorem nativeHeatQ3RefinedCarrierSourceCenterQuadraticMoment_theta (ns : ℕ) [NeZero ns]
    (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero)
    (m : ℤ) (hstate : nativeInductionState M h (m + 1))
    (k : ℕ) (hk20 : k ≤ 20) :
    ∫⁻ ω, ENNReal.ofReal
      (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ k)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M ^ k * (((nativeHeatGenQm ns).getD k 0 : ℚ) : ℝ)) := by
  let f : Cutoff.CutoffSample 2 → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (nativeHeatRefinedGridQuadraticGen ns M (m + 1) ω ^ k)
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp
      ((nativeHeatRefined_gridQuadratic_measurableGen ns M (m + 1)).pow_const k)
  have htransfer := nativeHeat_cutoff_lintegral_translate_scale_shift M
    (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) (m + 10) f hf
  calc
    _ = ∫⁻ ω, f (ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma (m + 10)
        (Cutoff.translateCutoffSample
          (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) ω))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      apply lintegral_congr
      intro ω
      simp only [f, nativeHeatRefined_centerQuadratic_eq_gridGen]
    _ = ∫⁻ ω, f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := htransfer
    _ ≤ _ := nativeHeatRefined_gridMoment_lintegral_le_theta ns hnum M h hM (m + 1)
      hgamma hstate k hk20

end ASDExplicitGamma.Native
