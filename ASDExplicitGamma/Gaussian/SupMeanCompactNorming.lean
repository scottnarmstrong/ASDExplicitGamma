module

public import ASDExplicitGamma.Gaussian.SupMeanNormingSequence
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Data.Nat.Pairing

/-! Fixed countable linear observations of genuine compact tensor suprema. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Set TopologicalSpace
open scoped RealInnerProductSpace
noncomputable section
section
variable {K E : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
  [SecondCountableTopology K] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SecondCountableTopology E]

/-- A sample-independent countable linear observation of a compact tensor field. -/
def supMeanCompactProjection (Z : C(K,E)) (n : ℕ) : ℝ :=
  ⟪supMeanNormingVector E n.unpair.2, Z (denseSeq K n.unpair.1)⟫

/-- Every fixed observation is bounded by the actual compact supremum. -/
theorem supMean_compact_projection_le (Z : C(K,E)) (n : ℕ) :
    supMeanCompactProjection Z n ≤ ‖Z‖ := by
  exact (real_inner_le_norm _ _).trans
    (((mul_le_mul_of_nonneg_right (supMean_norming_vector_norm_le E _) (norm_nonneg _)).trans_eq
      (one_mul _)).trans (Z.norm_coe_le_norm _))

/-- The actual compact tensor supremum is the supremum of fixed countably many
linear observations, simultaneously for every continuous sample. -/
theorem supMean_compact_norm_eq_countable (Z : C(K,E)) :
    ‖Z‖ = ⨆ n : ℕ, supMeanCompactProjection Z n := by
  have hb : BddAbove (range (supMeanCompactProjection Z)) :=
    ⟨‖Z‖, by rintro y ⟨n,rfl⟩; exact supMean_compact_projection_le Z n⟩
  apply le_antisymm ?_ (ciSup_le (supMean_compact_projection_le Z))
  have hpoint (m : ℕ) : ‖Z (denseSeq K m)‖ ≤ ⨆ n : ℕ, supMeanCompactProjection Z n := by
    rw [supMean_norm_eq_countable_inner]
    apply ciSup_le
    intro a
    have hh := le_ciSup hb (Nat.pair m a)
    simpa only [supMeanCompactProjection, Nat.unpair_pair] using! hh
  have hall : ∀ x : K, ‖Z x‖ ≤ ⨆ n : ℕ, supMeanCompactProjection Z n := by
    intro x
    exact (denseRange_denseSeq K).induction_on x
      (isClosed_le Z.continuous.norm continuous_const) hpoint
  have hn : 0 ≤ ⨆ n : ℕ, supMeanCompactProjection Z n :=
    (norm_nonneg (Z (Classical.choice inferInstance))).trans (hall _)
  exact (ContinuousMap.norm_le Z hn).mpr hall

end
end
end ASDExplicitGamma.Gaussian
