module

public import ASDExplicitGamma.Inverse.WeightedLocalizationZero
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Coloring costs only the square root of the number of colors in the variance term. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Exact Cauchy--Schwarz payment for the deterministic color classes. -/
theorem localization_color_sqrt_sum {κ : Type*} [Fintype κ] (V : κ → ℝ) (hV : ∀ j, 0 ≤ V j) :
    (∑ j, Real.sqrt (V j)) ≤ Real.sqrt (∑ j, V j) * Real.sqrt (Fintype.card κ : ℝ) := by
  simpa only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_id] using Real.sum_sqrt_mul_sqrt_le Finset.univ hV (fun _ : κ => (by norm_num : (0 : ℝ) ≤ 1))

/-- The source colored centered-sum bound, at every real order p>=1. No
independence between different colors is required. -/
theorem localization_colored_Lp {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : ι → Ω → ℝ) (c : ι → κ)
    (hind : ∀ j : κ, iIndepFun (fun i : {i // c i = j} => X i.1) mu)
    (hm : ∀ i, Measurable (X i)) (b p : ℝ) (hb : 0 ≤ b) (hp : 1 ≤ p)
    (hbound : ∀ i, ∀ᵐ ω ∂mu, |X i ω| ≤ b) (hmean : ∀ i, ∫ ω, X i ω ∂mu = 0)
    (V : κ → ℝ) (hV : ∀ j, 0 ≤ V j)
    (hvar : ∀ j, (∑ i : {i // c i = j}, moment (X i.1) 2 mu) ≤ V j) :
    eLpNorm (fun ω => ∑ i, X i ω) (ENNReal.ofReal p) mu ≤
      ENNReal.ofReal (2 * Real.sqrt p * Real.sqrt (∑ j, V j) * Real.sqrt (Fintype.card κ : ℝ) +
        2 * b * p * (Fintype.card κ : ℝ)) := by
  let C : κ → Ω → ℝ := fun j ω => ∑ i : {i // c i = j}, X i.1 ω
  have hc (j : κ) : eLpNorm (C j) (ENNReal.ofReal p) mu ≤
      ENNReal.ofReal (2 * Real.sqrt (V j) * Real.sqrt p + 2 * b * p) :=
    localization_independent_Lp_nonneg mu _ Finset.univ (hind j) (fun i => hm i.1)
      b (V j) p hb (hV j) hp (fun i _ => hbound i.1) (fun i _ => hmean i.1) (hvar j)
  have he : (fun ω => ∑ i, X i ω) = ∑ j, C j := by
    funext ω
    simp only [Finset.sum_apply, C]
    exact (Fintype.sum_fiberwise c (fun i => X i ω)).symm
  rw [he]
  apply (eLpNorm_sum_le (ENNReal.one_le_ofReal.mpr hp)).trans
  calc
    _ ≤ ∑ j, ENNReal.ofReal (2 * Real.sqrt (V j) * Real.sqrt p + 2 * b * p) :=
      Finset.sum_le_sum (fun j _ => hc j)
    _ = ENNReal.ofReal (∑ j, (2 * Real.sqrt (V j) * Real.sqrt p + 2 * b * p)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hs := mul_le_mul_of_nonneg_left (localization_color_sqrt_sum V hV)
        (show 0 ≤ 2 * Real.sqrt p by positivity)
      have hid : (∑ j, (2 * Real.sqrt (V j) * Real.sqrt p + 2 * b * p)) =
          2 * Real.sqrt p * (∑ j, Real.sqrt (V j)) + 2 * b * p * (Fintype.card κ : ℝ) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      rw [hid]
      nlinarith only [hs]

end ASDExplicitGamma.Inverse
