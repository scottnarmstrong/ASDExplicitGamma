module

public import ASDExplicitGamma.Gaussian.SupMeanCountableConcentration
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! A fixed countable family of unit-ball projections realizes the exact tensor norm. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped RealInnerProductSpace
noncomputable section
section
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E]

private instance supMeanNormingBallNonempty : Nonempty (Metric.closedBall (0:E) 1) :=
  ⟨⟨0,by simp⟩⟩

/-- The countable norming projections are fixed independently of the sample. -/
def supMeanNormingVector (n : ℕ) : E :=
  (denseSeq (Metric.closedBall (0:E) 1) n).val

omit [InnerProductSpace ℝ E] in
theorem supMean_norming_vector_norm_le (n : ℕ) : ‖supMeanNormingVector E n‖ ≤ 1 := by
  simpa only [supMeanNormingVector, Metric.mem_closedBall, dist_zero_right] using
    (denseSeq (Metric.closedBall (0:E) 1) n).property

/-- The tensor norm is the exact supremum of countably many linear observations. -/
theorem supMean_norm_eq_countable_inner (v : E) :
    ‖v‖ = ⨆ n : ℕ, ⟪supMeanNormingVector E n, v⟫ := by
  have hb : BddAbove (Set.range (fun n : ℕ => ⟪supMeanNormingVector E n, v⟫)) := by
    refine ⟨‖v‖, ?_⟩
    rintro y ⟨n,rfl⟩
    exact (real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right (supMean_norming_vector_norm_le E n) (norm_nonneg v)).trans_eq (one_mul _))
  apply le_antisymm ?_ (ciSup_le fun n => by
    exact (real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right (supMean_norming_vector_norm_le E n) (norm_nonneg v)).trans_eq (one_mul _)))
  by_cases hv : v = 0
  · subst v
    simp only [norm_zero, inner_zero_right, ciSup_const]
    exact le_rfl
  have hall : ∀ u : Metric.closedBall (0:E) 1,
      ⟪u.val,v⟫ ≤ ⨆ n : ℕ, ⟪supMeanNormingVector E n,v⟫ := by
    intro u
    refine (denseRange_denseSeq (Metric.closedBall (0:E) 1)).induction_on
      (p := fun z => ⟪z.val,v⟫ ≤ ⨆ n : ℕ, ⟪supMeanNormingVector E n,v⟫) u ?_ ?_
    · exact isClosed_le (continuous_subtype_val.inner continuous_const) continuous_const
    · intro n
      exact le_ciSup hb n
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]
  have hh := hall ⟨‖v‖⁻¹ • v, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu⟩
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at hh
  have he : ‖v‖⁻¹ * ‖v‖^2 = ‖v‖ := by field_simp
  simpa only [he] using hh

end
end
end ASDExplicitGamma.Gaussian
