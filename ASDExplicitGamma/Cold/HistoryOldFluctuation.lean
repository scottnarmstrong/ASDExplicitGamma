module

public import ASDExplicitGamma.Cold.ColdPositiveFluctuation

/-! # Safe conversion from the sharp root fluctuation to the old history branch -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Cold

/-- Raising a deterministic centering threshold decreases the positive fluctuation norm. -/
theorem cold_positive_threshold_mono {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] {X : Ω → ℝ} (hX : MemLp X 20 ℙ) {D a : ℝ} (hDa : D ≤ a) :
    lpNorm (fun ω => max (X ω-a) 0) 20 ℙ ≤ lpNorm (fun ω => max (X ω-D) 0) 20 ℙ := by
  apply cold_lpNorm_mono_ae ((hX.sub (memLp_const D)).pos_part)
  filter_upwards with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  exact max_le_max (sub_le_sub_left hDa _) le_rfl

/-- The source old branch has the safe crude coefficient four, with the same raw cap R. -/
theorem cold_root_centered_le_old {R : ℝ} (hR : 0 ≤ R) {d : ℕ} (hd : 0 < d) :
    coldCenteredMomentCap R d ≤ R*min 1 (4*Real.sqrt 19*(3:ℝ)^(-(d:ℝ))) := by
  rw [coldCenteredMomentCap,ite_eq_right (Nat.ne_of_gt hd),mul_min_of_nonneg _ _ hR,mul_one]
  apply min_le_min (le_refl _)
  have hs : 0 ≤ Real.sqrt 19 := Real.sqrt_nonneg _
  have hp : 0 ≤ (3:ℝ)^(-(d:ℝ)) := Real.rpow_nonneg (by norm_num) _
  nlinarith only [mul_nonneg (mul_nonneg hR hs) hp]

end ASDExplicitGamma.Cold
