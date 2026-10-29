module

public import ASDExplicitGamma.Inverse.StoppedOmittedCost
public import ASDExplicitGamma.Inverse.StoppedOmittedGeometry
public import ASDExplicitGamma.Inverse.StoppedDiameterRarity

/-! The complete omitted-label probability, retaining nine candidates and every raw site. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

theorem positive_occupancy_shift_summable (M : ℕ) :
    Summable (fun k : ℕ => positiveOccupancyCost (M+k)) := by
  have hg := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left (9*Real.exp (-6120))
  have hs := hg.summable.of_nonneg_of_le (fun k => by unfold positiveOccupancyCost; positivity)
    positive_occupancy_majorant
  have hi : Function.Injective (fun k : ℕ => M+k) := by intro i k he; exact Nat.add_left_cancel he
  exact hs.comp_injective hi

/-- All omitted activations meeting inspection cost at most exp(-N), N=3^M.
The count is nine aligned cubes per label times their full side-squared raw
population, not a count of hypothetical independent labels. -/
theorem omitted_activation_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (M : ℕ) (x : BlockSite) :
    μ.real (omittedActivation B M (3^M) x) ≤ Real.exp (-(3:ℝ)^M) := by
  let E (k : ℕ) : Set Ω := ⋃ i ∈ blockBox (alignedCubeIndex (3^(M+k+1)) x), positiveActivation B (M+k) i
  have hE (k : ℕ) : μ.real (E k) ≤ 9*positiveOccupancyCost (M+k) := by
    calc
      _ ≤ ∑ i ∈ blockBox (alignedCubeIndex (3^(M+k+1)) x), μ.real (positiveActivation B (M+k) i) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ blockBox (alignedCubeIndex (3^(M+k+1)) x), positiveOccupancyCost (M+k) :=
        Finset.sum_le_sum fun i _ => control_activation_probability μ B q hB (M+k) i
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,block_box_card]; norm_num
  have hu := countable_union_probability_le μ E (fun k => 9*positiveOccupancyCost (M+k))
    (fun k => by unfold positiveOccupancyCost; positivity)
    ((positive_occupancy_shift_summable M).mul_left 9) hE
  rw [tsum_mul_left] at hu
  exact (measureReal_mono (omitted_activation_subset_candidates B M x) (measure_ne_top μ _)).trans
    (hu.trans (omitted_positive_cost_sum M))

end
end ASDExplicitGamma.Inverse
