module

public import ASDExplicitGamma.Inverse.HistoryPopulation
public import ASDExplicitGamma.Numerics.Inverse.RealBounds

/-! Positive truncation and finite-population payment, without independence. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal

/-- The actual positive remainder after paying the deterministic slack. -/
def positiveSplitRemainder (Y A δ : ℝ) : ℝ := max 0 (Y - A - δ)

theorem positive_split (Y A δ : ℝ) :
    0 ≤ positiveSplitRemainder Y A δ ∧ Y ≤ A + δ + positiveSplitRemainder Y A δ := by
  unfold positiveSplitRemainder
  exact ⟨le_max_left _ _, by linarith only [le_max_right (0 : ℝ) (Y - A - δ)]⟩

/-- Universal quadratic truncation applied to the positive excess over A. -/
theorem positive_split_quadratic (Y A δ : ℝ) (hδ : 0 < δ) :
    positiveSplitRemainder Y A δ ≤ (max 0 (Y - A)) ^ 2 / (4 * δ) := by
  have h := Numerics.Inverse.inv_positive_quadratic (max 0 (Y - A)) δ hδ
  apply le_trans _ h
  unfold positiveSplitRemainder
  exact max_le_max le_rfl (by linarith only [le_max_right (0 : ℝ) (Y - A)])

/-- Paying delta turns a 256-moment excess into a 128-moment remainder. -/
theorem positive_split_L128 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (A δ : ℝ) (hδ : 0 < δ) :
    eLpNorm (fun ω => positiveSplitRemainder (Y ω) A δ) 128 μ ≤
      ENNReal.ofReal (1 / (4 * δ)) *
        (eLpNorm (fun ω => max 0 (Y ω - A)) 256 μ) ^ 2 := by
  let X : Ω → ℝ := fun ω => max 0 (Y ω - A)
  have hX : Measurable X := measurable_const.max (hY.sub_const A)
  have hp : eLpNorm (fun ω => ‖X ω‖ ^ (2 : ℕ)) 128 μ = (eLpNorm X 256 μ) ^ 2 := by
    have hh := eLpNorm_norm_rpow (μ := μ) (p := 128) X hX.aestronglyMeasurable (by norm_num : (0 : ℝ) < 2)
    norm_num only [ENNReal.ofReal_ofNat, show (128 : ℝ≥0∞) * 2 = 256 by norm_num,
      Real.rpow_two, ENNReal.rpow_two] at hh
    exact hh
  have he : (fun ω => ‖X ω‖ ^ (2 : ℕ)) = (fun ω => X ω ^ 2) := by
    funext ω
    rw [Real.norm_eq_abs, sq_abs]
  rw [he] at hp
  calc
    _ ≤ eLpNorm ((1 / (4 * δ)) • (fun ω => X ω ^ 2)) 128 μ := by
      apply eLpNorm_mono_ae_real
        ((measurable_const.max ((hY.sub_const A).sub_const δ)).aestronglyMeasurable)
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
        simpa only [positiveSplitRemainder, X, Pi.smul_apply, smul_eq_mul, one_div, div_eq_mul_inv, one_mul, mul_comm] using
          positive_split_quadratic (Y ω) A δ hδ
    _ = _ := by
      rw [eLpNorm_const_smul, Real.enorm_of_nonneg (by positivity), hp]

/-- Apply a supplied excess budget, retaining the exact quadratic slack cost. -/
theorem positive_split_L128_of_cap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (A δ : ℝ) (hδ : 0 < δ) (e : ℝ≥0∞)
    (he : eLpNorm (fun ω => max 0 (Y ω - A)) 256 μ ≤ e) :
    eLpNorm (fun ω => positiveSplitRemainder (Y ω) A δ) 128 μ ≤
      ENNReal.ofReal (1 / (4 * δ)) * e ^ 2 :=
  (positive_split_L128 μ Y hY A δ hδ).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left' he 2) (zero_le : (0 : ℝ≥0∞) ≤ _))

end ASDExplicitGamma.Inverse
