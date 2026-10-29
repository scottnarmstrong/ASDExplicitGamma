module

public import ASDExplicitGamma.Gaussian.SpatialLpFourth
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Spatial L⁴ moments and probability/spatial Fubini -/

@[expose] public section

open MeasureTheory

namespace ASDExplicitGamma.Gaussian

/-- The canonical inclusion of continuous functions retains the ordinary fourth moment. -/
theorem continuousMap_toLp_norm_pow_four {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν] (f : C(K, ℝ)) :
    ‖ContinuousMap.toLp 4 ν ℝ f‖ ^ 4 = ∫ x, f x ^ 4 ∂ν := by
  rw [lp4_norm_pow_four]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 4) ν (𝕜 := ℝ) f] with x hx
  exact congrArg (fun r : ℝ => r ^ 4) hx

/-- A finite C(K)-valued fourth moment suffices for the exact probability/spatial Fubini
identity. No independence between spatial points is assumed. -/
theorem integral_spatialLp4_norm_pow_four {Ω K : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] (μ : Measure Ω) [SFinite μ]
    (ν : Measure K) [IsFiniteMeasure ν] (F : Ω → C(K, ℝ)) (hF : MemLp F 4 μ) :
    (∫ ω, ‖ContinuousMap.toLp 4 ν ℝ (F ω)‖ ^ 4 ∂μ) =
      ∫ x, ∫ ω, F ω x ^ 4 ∂μ ∂ν := by
  have hpow : Integrable (fun ω => ‖F ω‖ ^ (4 : ℕ)) μ := by
    have hh := hF.integrable_norm_rpow (by norm_num) (by norm_num)
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at hh
    exact hh
  have hmajor : Integrable (fun z : Ω × K => ‖F z.1‖ ^ (4 : ℕ)) (μ.prod ν) :=
    hpow.comp_fst ν
  have hm : AEStronglyMeasurable (fun z : Ω × K => F z.1 z.2 ^ (4 : ℕ)) (μ.prod ν) := by
    have hh := continuous_eval.comp_aestronglyMeasurable
      ((hF.aestronglyMeasurable.comp_fst (ν := ν)).prodMk
        (measurable_snd.stronglyMeasurable.aestronglyMeasurable :
          AEStronglyMeasurable (fun z : Ω × K => z.2) (μ.prod ν)))
    exact hh.pow 4
  have hi : Integrable (fun z : Ω × K => F z.1 z.2 ^ (4 : ℕ)) (μ.prod ν) := by
    refine hmajor.mono' hm (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, ← pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (ContinuousMap.norm_coe_le_norm (F z.1) z.2) 4
  simp_rw [continuousMap_toLp_norm_pow_four]
  exact integral_integral_swap hi

end ASDExplicitGamma.Gaussian
