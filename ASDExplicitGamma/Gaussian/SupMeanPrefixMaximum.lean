module

public import ASDExplicitGamma.Gaussian.SupMeanFiniteConcentration

/-! Prefix maxima converge in mean to an integrable Gaussian supremum. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section

/-- Prefix maxima always include observation zero. -/
def supMeanPrefixMaximum {Ω : Type*} (X : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℝ :=
  supMeanGaussianMaximum (Nat.zero_lt_succ N) (fun i : Fin (N+1) => X i.val)

/-- A prefix maximum lies below the finite countable supremum. -/
theorem supMean_prefix_le_sup {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) (hb : BddAbove (Set.range fun k => X k ω)) :
    supMeanPrefixMaximum X N ω ≤ gaussianRealizationSup X ω := by
  unfold supMeanPrefixMaximum supMeanGaussianMaximum gaussianRealizationSup
  apply Finset.sup'_le
  intro i _
  exact le_csSup hb (Set.mem_range_self i.val)

/-- Exhaustion by actual finite maxima converges pointwise whenever the countable
family is bounded above. -/
theorem supMean_prefix_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (ω : Ω) (hb : BddAbove (Set.range fun k => X k ω)) :
    Tendsto (fun N => supMeanPrefixMaximum X N ω) atTop (𝓝 (gaussianRealizationSup X ω)) := by
  apply tendsto_order.mpr
  constructor
  · intro b h
    obtain ⟨y, ⟨k,rfl⟩, hky⟩ := (lt_csSup_iff hb (Set.range_nonempty _)).mp h
    filter_upwards [eventually_ge_atTop k] with N hN
    have ht : X k ω ≤ supMeanPrefixMaximum X N ω := by
      exact Finset.le_sup' (f := fun i : Fin (N+1) => X i.val ω)
        (Finset.mem_univ ⟨k,by omega⟩)
    exact hky.trans_le ht
  · intro b h
    exact Eventually.of_forall fun N => (supMean_prefix_le_sup X N ω hb).trans_lt h

/-- An integrable countable supremum controls its actual Gaussian prefix means. -/
theorem supMean_prefix_means_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) (L : ℝ) (hL : 0 ≤ L)
    (hvar : ∀ k, Var[X k; μ] ≤ L^2)
    (hInt : Integrable (gaussianRealizationSup X) μ)
    (hb : ∀ᵐ ω ∂μ, BddAbove (Set.range fun k => X k ω)) :
    Tendsto (fun N => ∫ ω, supMeanPrefixMaximum X N ω ∂μ) atTop
      (𝓝 (∫ ω, gaussianRealizationSup X ω ∂μ)) := by
  have hM (N : ℕ) : Integrable (supMeanPrefixMaximum X N) μ :=
    (supMean_gaussian_maximum_mgf μ (Nat.zero_lt_succ N) (fun i : Fin (N+1) => X i.val)
      (hX.comp Fin.val) L 0 hL (fun i => hvar i.val)).1
  have h0 : Integrable (X 0) μ := memLp_one_iff_integrable.mp (hX.memLp 0 1 (by simp))
  have hdom : Integrable (fun ω => |gaussianRealizationSup X ω| + |X 0 ω|) μ := by
    simpa only [Real.norm_eq_abs, Pi.add_apply] using! hInt.norm.add h0.norm
  apply tendsto_integral_of_dominated_convergence _ (fun N => (hM N).aestronglyMeasurable) hdom
  · intro N
    filter_upwards [hb] with ω hω
    have hlo : X 0 ω ≤ supMeanPrefixMaximum X N ω :=
      Finset.le_sup' (f := fun i : Fin (N+1) => X i.val ω) (Finset.mem_univ ⟨0,by omega⟩)
    have hhi := supMean_prefix_le_sup X N ω hω
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith only [hlo, neg_abs_le (X 0 ω), abs_nonneg (gaussianRealizationSup X ω)]
    · linarith only [hhi, le_abs_self (gaussianRealizationSup X ω), abs_nonneg (X 0 ω)]
  · filter_upwards [hb] with ω hω
    exact supMean_prefix_tendsto X ω hω

end
end ASDExplicitGamma.Gaussian
