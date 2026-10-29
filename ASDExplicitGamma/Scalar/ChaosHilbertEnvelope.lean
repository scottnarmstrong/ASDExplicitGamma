module

public import ASDExplicitGamma.Scalar.ChaosEnvelopeLimit

/-! Corrected SC-CHAOS-MOMENT-BOUND for the actual infinite-input Hilbert Gaussian envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- The source second-moment constant survives the controlled Gaussian finite-rank passage. -/
theorem gaussian_hilbert_envelope_second_moment (m : W) (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) :
    (∫ omega,(gaussianHilbertEnvelope m B v hA omega)^2 ∂Gaussian.standardGaussianInfinitePi)≤
      (1+Real.sqrt 15)^2*(∫ omega,gaussianHilbertEnvelope m B v hA omega ∂Gaussian.standardGaussianInfinitePi)^2 := by
  have h := gaussian_hilbert_envelope_moment_limits m B v hA
  exact le_of_tendsto_of_tendsto h.2.2.2 ((h.2.2.1.pow 2).const_mul ((1+Real.sqrt 15)^2))
    (Eventually.of_forall (fun k => (gaussian_bilinear_partial_moment_bound m B v (Gaussian.gaussianFastIndex hA k)).2.2))

/-- SC-CHAOS-MOMENT-BOUND with conjugate exponent q=p/(p−1), for arbitrary Hilbert outputs
and the actual countable Gaussian realization; no moment bound is a premise. -/
theorem gaussian_hilbert_envelope_conjugate_bound (m : W) (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) (p : ℝ) (hp : 2≤p) :
    eLpNorm (gaussianHilbertEnvelope m B v hA) (ENNReal.ofReal (p/(p-1))) Gaussian.standardGaussianInfinitePi≤
      ENNReal.ofReal ((1+Real.sqrt 15)^(2/p)*
        (∫ omega,gaussianHilbertEnvelope m B v hA omega ∂Gaussian.standardGaussianInfinitePi)) := by
  have h := gaussian_hilbert_envelope_moment_limits m B v hA
  exact chaos_norm_of_real_second_moment _ _ (measurable_gaussian_hilbert_envelope m B v hA)
    (fun omega => sq_nonneg _) h.1 h.2.1 _ chaos_envelope_constants.1.le p hp
    (gaussian_hilbert_envelope_second_moment m B v hA)

end ASDExplicitGamma.Scalar
