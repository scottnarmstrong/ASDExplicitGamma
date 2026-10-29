module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Integrable envelopes for the sharp twentieth-moment sum estimate -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ASDExplicitGamma.Gaussian

/-- Lower powers have a uniform integrable twentieth-power envelope. -/
theorem rio_power_le_one_add_twentieth {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≤ 20) :
    x^n ≤ 1+x^20 := by
  by_cases h : x ≤ 1
  · have hp := pow_le_pow_left₀ hx h n
    simpa only [one_pow] using hp.trans (le_add_of_nonneg_right (pow_nonneg hx 20))
  · have hp := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) hn
    exact hp.trans (le_add_of_nonneg_left (by norm_num))

/-- The product of two powers admits the same envelope when their degrees total at most twenty. -/
theorem rio_mixed_power_bound {x y W : ℝ} (hW : 0 ≤ W) (hx : |x| ≤ W) (hy : |y| ≤ W)
    {n m : ℕ} (hnm : n+m ≤ 20) : |x^n*y^m| ≤ 1+W^20 := by
  rw [abs_mul,abs_pow,abs_pow]
  calc
    _ ≤ W^n*W^m := mul_le_mul (pow_le_pow_left₀ (abs_nonneg x) hx n)
      (pow_le_pow_left₀ (abs_nonneg y) hy m) (pow_nonneg (abs_nonneg _) _) (pow_nonneg hW _)
    _ = W^(n+m) := (pow_add _ _ _).symm
    _ ≤ _ := rio_power_le_one_add_twentieth hW hnm

/-- One nonnegative L20 envelope controls all powers used in differentiating twice. -/
theorem rio_integrable_mixed_power {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] {S X : Ω → ℝ} (hS : MemLp S 20 ℙ) (hX : MemLp X 20 ℙ)
    (t : ℝ) {n m : ℕ} (hnm : n+m ≤ 20) :
    Integrable (fun ω => (S ω+t*X ω)^n*X ω^m) ℙ := by
  let W := fun ω => |S ω+t*X ω|+|X ω|
  have hY : MemLp (fun ω => S ω+t*X ω) 20 ℙ := hS.add (hX.const_mul t)
  have hW : MemLp W 20 ℙ := hY.norm.add hX.norm
  have hWi : Integrable (fun ω => W ω^20) ℙ := by
    have h := hW.integrable_norm_pow (p := 20) (by norm_num)
    simpa only [Real.norm_eq_abs,show (20:ℕ)=2*10 by norm_num,pow_mul,sq_abs] using h
  have hm : AEStronglyMeasurable (fun ω => (S ω+t*X ω)^n*X ω^m) ℙ :=
    (hY.aestronglyMeasurable.pow n).mul (hX.aestronglyMeasurable.pow m)
  apply ((integrable_const 1).add hWi).mono' hm
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact rio_mixed_power_bound (by positivity)
    (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _)) hnm

end ASDExplicitGamma.Gaussian
