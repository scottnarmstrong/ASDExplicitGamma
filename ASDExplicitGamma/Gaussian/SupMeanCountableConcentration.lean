module

public import ASDExplicitGamma.Gaussian.SupMeanPrefixMaximum
public import ASDExplicitGamma.Gaussian.SupMeanNonnegativeLimit

/-! Sharp MGF concentration survives the passage to an actual countable Gaussian supremum. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section

/-- Sharp centered MGF for an integrable countable jointly Gaussian supremum.
No exponential integrability or finite-dimensional realization premise is assumed. -/
theorem supMean_gaussian_countable_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) (L lam : ℝ) (hL : 0 ≤ L)
    (hvar : ∀ k, Var[X k; μ] ≤ L^2)
    (hInt : Integrable (gaussianRealizationSup X) μ)
    (hb : ∀ᵐ ω ∂μ, BddAbove (Set.range fun k => X k ω)) :
    Integrable (fun ω => Real.exp (lam*(gaussianRealizationSup X ω-
      ∫ y, gaussianRealizationSup X y ∂μ))) μ ∧
    (∫ ω, Real.exp (lam*(gaussianRealizationSup X ω-
      ∫ y, gaussianRealizationSup X y ∂μ)) ∂μ) ≤ Real.exp (lam^2*L^2/2) := by
  let F (N : ℕ) (ω : Ω) := Real.exp (lam*(supMeanPrefixMaximum X N ω-
    ∫ y, supMeanPrefixMaximum X N y ∂μ))
  have hF (N : ℕ) := supMean_gaussian_maximum_mgf μ (Nat.zero_lt_succ N)
    (fun i : Fin (N+1) => X i.val) (hX.comp Fin.val) L lam hL (fun i => hvar i.val)
  have hm := supMean_prefix_means_tendsto μ X hX L hL hvar hInt hb
  apply supMean_nonnegative_integral_limit μ F _ (Real.exp (lam^2*L^2/2)) (Real.exp_pos _).le
    (fun N => (hF N).2.2.1) (fun N => Eventually.of_forall fun ω => (Real.exp_pos _).le)
    (Eventually.of_forall fun ω => (Real.exp_pos _).le) (fun N => (hF N).2.2.2)
  filter_upwards [hb] with ω hω
  exact Real.continuous_exp.continuousAt.tendsto.comp
    (tendsto_const_nhds.mul ((supMean_prefix_tendsto X ω hω).sub hm))

end
end ASDExplicitGamma.Gaussian
