module

public import ASDExplicitGamma.Gaussian.SpatialFourthMoment
public import ASDExplicitGamma.Gaussian.MeanFourthMoment

/-! # The spatial Gaussian norm's mean from pointwise fourth moments -/

@[expose] public section

open MeasureTheory

namespace ASDExplicitGamma.Gaussian

/-- Fubini and probability L¹-to-L⁴ monotonicity turn a uniform pointwise fourth-moment cap
into the exact mean bound for the ordinary spatial norm. -/
theorem spatialLp4_mean_sq_le_of_point_moment {Ω K : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure K) [IsFiniteMeasure ν] (F : Ω → C(K, ℝ)) (hF : MemLp F 4 μ)
    {C : ℝ} (hpoint : ∀ x, (∫ ω, F ω x ^ 4 ∂μ) ≤ C) :
    (∫ ω, ‖ContinuousMap.toLp 4 ν ℝ (F ω)‖ ∂μ) ^ 2 ≤ Real.sqrt (ν.real Set.univ * C) := by
  have hZ : MemLp (fun ω => ‖ContinuousMap.toLp 4 ν ℝ (F ω)‖) 4 μ :=
    (hF.continuousLinearMap_comp (ContinuousMap.toLp 4 ν ℝ)).norm
  have hmean := integral_sq_le_sqrt_fourthMoment μ _ (fun ω => norm_nonneg _) hZ
  apply hmean.trans
  apply Real.sqrt_le_sqrt
  rw [integral_spatialLp4_norm_pow_four μ ν F hF]
  calc
    _ ≤ ∫ _ : K, C ∂ν := integral_mono_of_nonneg
      (ae_of_all _ fun x => integral_nonneg fun ω => by positivity)
      (integrable_const C) (ae_of_all _ hpoint)
    _ = _ := by rw [integral_const, smul_eq_mul]

end ASDExplicitGamma.Gaussian
