module

public import ASDExplicitGamma.Gaussian.TimeContinuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # GA-TWO-PARAM: the C¹ identity and its endpoint derivatives -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- The two-parameter expectation with both endpoints. The old law has only its source polynomial moments; the
fresh series can be any joint bounded image, including restrictions, centerings and products. -/
theorem c1On_timeHeatAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (ν : Measure E) [IsFiniteMeasure ν]
    (hν : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) ν)
    {G D : ℝ → E → ℝ} (hG : TimeRegularity G D) :
    ContinuousOn (timeHeatAverage hA T ν G) (Icc 0 1) ∧
    ContinuousOn (timeHeatDerivative hA T ν G D) (Icc 0 1) ∧
    (∀ t ∈ Ioo 0 1, HasDerivAt (timeHeatAverage hA T ν G)
      (timeHeatDerivative hA T ν G D t) t) ∧
    HasDerivWithinAt (timeHeatAverage hA T ν G)
      (timeHeatDerivative hA T ν G D 0) (Icc 0 1) 0 ∧
    HasDerivWithinAt (timeHeatAverage hA T ν G)
      (timeHeatDerivative hA T ν G D 1) (Icc 0 1) 1 := by
  have hc := continuousOn_timeHeatAverage_and_derivative hA T ν hν hG
  have hd := fun {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) =>
    hasDerivAt_timeHeatAverage hA T ν hν hG ht
  have hdiff : DifferentiableOn ℝ (timeHeatAverage hA T ν G) (Ioo 0 1) :=
    fun t ht => (hd ht).differentiableAt.differentiableWithinAt
  refine ⟨hc.1, hc.2, fun t ht => hd ht, ?_, ?_⟩
  · have hlim := (hc.2 0 ⟨le_refl _, zero_le_one⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) Ioo_subset_Icc_self)
    have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ), deriv (timeHeatAverage hA T ν G) t =
        timeHeatDerivative hA T ν G D t :=
      by
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
        exact (hd ht).deriv
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
      ((hc.1 0 ⟨le_refl _, zero_le_one⟩).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
      (hlim.congr' (heq.mono fun _ h => h.symm))).mono Icc_subset_Ici_self
  · have hlim := (hc.2 1 ⟨zero_le_one, le_refl _⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) Ioo_subset_Icc_self)
    have heq : ∀ᶠ t in 𝓝[<] (1 : ℝ), deriv (timeHeatAverage hA T ν G) t =
        timeHeatDerivative hA T ν G D t :=
      by
        filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
        exact (hd ht).deriv
    exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
      ((hc.1 1 ⟨zero_le_one, le_refl _⟩).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
      (hlim.congr' (heq.mono fun _ h => h.symm))).mono Icc_subset_Iic_self

end ASDExplicitGamma.Gaussian
