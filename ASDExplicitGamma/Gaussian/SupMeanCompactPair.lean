module

public import ASDExplicitGamma.Gaussian.SupMeanCompactNorming

/-! A sum of two actual tensor suprema is one fixed countable Gaussian supremum. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Set
open scoped RealInnerProductSpace
noncomputable section
section
variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
  [SecondCountableTopology K] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [SecondCountableTopology F]

/-- Both locations and both norming directions are fixed independently of the sample. -/
def supMeanCompactPairProjection (Z : C(K,E)) (W : C(K,F)) (a b : ℝ) (n : ℕ) : ℝ :=
  a*supMeanCompactProjection Z n.unpair.1+b*supMeanCompactProjection W n.unpair.2

/-- The combined physical derivative functional is an actual countable linear
supremum, retaining the sum of its two Cameron-Martin constants. -/
theorem supMean_compact_pair_eq_countable (Z : C(K,E)) (W : C(K,F))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*‖Z‖+b*‖W‖ = ⨆ n : ℕ, supMeanCompactPairProjection Z W a b n := by
  have hbound (n : ℕ) : supMeanCompactPairProjection Z W a b n ≤ a*‖Z‖+b*‖W‖ :=
    add_le_add (mul_le_mul_of_nonneg_left (supMean_compact_projection_le Z _) ha)
      (mul_le_mul_of_nonneg_left (supMean_compact_projection_le W _) hb)
  have hbounded : BddAbove (range (supMeanCompactPairProjection Z W a b)) :=
    ⟨a*‖Z‖+b*‖W‖, by rintro y ⟨n,rfl⟩; exact hbound n⟩
  apply le_antisymm ?_ (ciSup_le hbound)
  have hseq (m n : ℕ) : a*supMeanCompactProjection Z m+b*supMeanCompactProjection W n ≤
      ⨆ q : ℕ, supMeanCompactPairProjection Z W a b q := by
    simpa only [supMeanCompactPairProjection, Nat.unpair_pair] using!
      le_ciSup hbounded (Nat.pair m n)
  have hm (m : ℕ) : a*supMeanCompactProjection Z m+b*‖W‖ ≤
      ⨆ q : ℕ, supMeanCompactPairProjection Z W a b q := by
    have hn : b*‖W‖ ≤ (⨆ q : ℕ, supMeanCompactPairProjection Z W a b q)-
        a*supMeanCompactProjection Z m := by
      rw [supMean_compact_norm_eq_countable W, Real.mul_iSup_of_nonneg hb]
      exact ciSup_le fun n => by linarith only [hseq m n]
    linarith only [hn]
  have hz : a*‖Z‖ ≤ (⨆ q : ℕ, supMeanCompactPairProjection Z W a b q)-b*‖W‖ := by
    rw [supMean_compact_norm_eq_countable Z, Real.mul_iSup_of_nonneg ha]
    exact ciSup_le fun m => by linarith only [hm m]
  linarith only [hz]

end
end
end ASDExplicitGamma.Gaussian
