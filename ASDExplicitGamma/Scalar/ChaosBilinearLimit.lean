module

public import ASDExplicitGamma.Scalar.ChaosBilinearMajorant

/-! Almost-sure convergence of the actual centered quadratic source cutoffs. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- The finite trace centerings converge on the same fast subsequence as the Gaussian field. -/
theorem gaussian_bilinear_trace_partial_tendsto (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (Gaussian.gaussianFastIndex hA k),B (v i) (v i)) atTop
      (nhds (gaussianBilinearTrace B v)) :=
  (gaussian_bilinear_trace_summable B v hA).hasSum.tendsto_sum_nat.comp
    (Gaussian.gaussianFastIndex_strictMono hA).tendsto_atTop

variable [CompleteSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [OpensMeasurableSpace V]

/-- The trace-centered Gaussian Hilbert quadratic is the actual limit of its finite cutoffs. -/
theorem ae_gaussian_bilinear_partial_tendsto (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) :
    ∀ᵐ omega ∂Gaussian.standardGaussianInfinitePi,
      Tendsto (fun k => gaussianBilinearPartial B v (Gaussian.gaussianFastIndex hA k) omega) atTop
        (nhds (gaussianBilinearChaos B v hA omega)) := by
  filter_upwards [Gaussian.ae_tendsto_gaussianSeriesLimit v hA] with omega hconv
  have hc : Continuous (fun x : V => B x x) := by fun_prop
  have h := (hc.tendsto (Gaussian.gaussianSeriesLimit v hA omega)).comp hconv
  exact h.sub (gaussian_bilinear_trace_partial_tendsto B v hA)

/-- The squared Hilbert-norm envelopes converge along the genuine source cutoffs. -/
theorem ae_gaussian_hilbert_envelope_partial_tendsto (m : W) (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) :
    ∀ᵐ omega ∂Gaussian.standardGaussianInfinitePi,
      Tendsto (fun k => ‖m+gaussianBilinearPartial B v (Gaussian.gaussianFastIndex hA k) omega‖^2) atTop
        (nhds (gaussianHilbertEnvelope m B v hA omega)) := by
  filter_upwards [ae_gaussian_bilinear_partial_tendsto B v hA] with omega hconv
  exact (hconv.const_add m).norm.pow 2

end ASDExplicitGamma.Scalar
