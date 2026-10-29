module

public import ASDExplicitGamma.Gaussian.SupMeanCompactPair

/-! Sharp concentration of the combined tensor supremum from its fixed observations. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory
noncomputable section

/-- A combined compact tensor supremum retains its single Gaussian Lipschitz
payment. The observation law and variance inputs are discharged by actual shell
kernel identities in the physical application. -/
theorem supMean_compact_pair_tail {Ω K E F : Type*} [MeasurableSpace Ω]
    [TopologicalSpace K] [CompactSpace K] [Nonempty K] [SecondCountableTopology K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [SecondCountableTopology F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → C(K,E)) (W : Ω → C(K,F))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hZ : Integrable (fun ω => ‖Z ω‖) μ) (hW : Integrable (fun ω => ‖W ω‖) μ)
    (hg : IsCenteredGaussianFamily μ (fun n ω => supMeanCompactPairProjection (Z ω) (W ω) a b n))
    (L t : ℝ) (hL : 0 < L) (ht : 0 ≤ t)
    (hv : ∀ n, Var[(fun ω => supMeanCompactPairProjection (Z ω) (W ω) a b n); μ] ≤ L^2) :
    μ.real {ω | t ≤ a*‖Z ω‖+b*‖W ω‖-∫ y, (a*‖Z y‖+b*‖W y‖) ∂μ} ≤
      Real.exp (-t^2/(2*L^2)) := by
  have he : gaussianRealizationSup (fun n ω => supMeanCompactPairProjection (Z ω) (W ω) a b n) =
      (fun ω => a*‖Z ω‖+b*‖W ω‖) := by
    funext ω
    exact (supMean_compact_pair_eq_countable (Z ω) (W ω) a b ha hb).symm
  have hi : Integrable (fun ω => a*‖Z ω‖+b*‖W ω‖) μ :=
    (hZ.const_mul a).add (hW.const_mul b)
  have hf : ∀ᵐ ω ∂μ, BddAbove (Set.range fun n =>
      supMeanCompactPairProjection (Z ω) (W ω) a b n) := by
    apply Filter.Eventually.of_forall
    intro ω
    refine ⟨a*‖Z ω‖+b*‖W ω‖, ?_⟩
    rintro y ⟨n,rfl⟩
    exact add_le_add (mul_le_mul_of_nonneg_left (supMean_compact_projection_le (Z ω) _) ha)
      (mul_le_mul_of_nonneg_left (supMean_compact_projection_le (W ω) _) hb)
  have hh := supMean_gaussian_countable_tail μ _ hg hL ht (by rw [he]; exact hi) hf hv
  simpa only [he] using hh

end
end ASDExplicitGamma.Gaussian
