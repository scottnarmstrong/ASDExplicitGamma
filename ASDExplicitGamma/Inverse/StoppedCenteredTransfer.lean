module

public import ASDExplicitGamma.Inverse.WeightedLocalizationLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Deterministic centering and weighted transfer from localized to full fields. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Centering costs at most twice the real-order norm on a probability space. -/
theorem centered_Lp_le_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : AEStronglyMeasurable X μ)
    (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => X ω-∫ ζ, X ζ ∂μ) (ENNReal.ofReal p) μ ≤
      2*eLpNorm X (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hmean : ‖∫ ζ, X ζ ∂μ‖ₑ ≤ eLpNorm X (ENNReal.ofReal p) μ := by
    apply (enorm_integral_le_lintegral_enorm X).trans
    rw [← eLpNorm_one_eq_lintegral_enorm hX]
    exact eLpNorm_le_eLpNorm_of_exponent_le hpE
  have hc : eLpNorm (fun _ : Ω => ∫ ζ, X ζ ∂μ) (ENNReal.ofReal p) μ = ‖∫ ζ, X ζ ∂μ‖ₑ := by
    rw [eLpNorm_const' _ (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top,
      measure_univ,ENNReal.one_rpow,mul_one]
  have hh := eLpNorm_sub_le (μ := μ) (f := X) (g := fun _ : Ω => ∫ ζ, X ζ ∂μ) hpE
  rw [hc] at hh
  exact hh.trans ((add_le_add le_rfl hmean).trans_eq (two_mul _).symm)

/-- Weighted full centered averages differ from their localized centered
averages by at most twice the weighted sum of individual localization errors.
All weights and the error budget are deterministic; no independence is used. -/
theorem weighted_centered_transfer {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : I → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) μ) (hY : ∀ i, Integrable (Y i) μ)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (C p : ℝ) (hC : 0 ≤ C) (hp : 1 ≤ p)
    (herror : ∀ i, eLpNorm (fun ω => X i ω-Y i ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => ∑ i, w i*(Y i ω-∫ ζ, Y i ζ ∂μ)) (ENNReal.ofReal p) μ+
        ENNReal.ofReal (2*C*(∑ i, w i)) := by
  let Z : I → Ω → ℝ := fun i ω => w i*((X i ω-Y i ω)-∫ ζ, X i ζ-Y i ζ ∂μ)
  have hpE : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hZ (i : I) : eLpNorm (Z i) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (2*C*w i) := by
    have hc := (centered_Lp_le_two μ (fun ω => X i ω-Y i ω)
      ((hX i).sub (hY i)).aestronglyMeasurable p hp).trans
        (mul_le_mul_of_nonneg_left (herror i) (zero_le : (0:ℝ≥0∞) ≤ 2))
    have hc' : eLpNorm (fun ω => (X i ω-Y i ω)-∫ ζ, X i ζ-Y i ζ ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2*C) := by
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat] using! hc
    have he : eLpNorm (Z i) (ENNReal.ofReal p) μ = ENNReal.ofReal (w i)*
        eLpNorm (fun ω => (X i ω-Y i ω)-∫ ζ, X i ζ-Y i ζ ∂μ) (ENNReal.ofReal p) μ := by
      simpa only [Z,Pi.smul_apply,smul_eq_mul,Real.enorm_eq_ofReal (hw i)] using!
        eLpNorm_const_smul (w i) (fun ω => (X i ω-Y i ω)-∫ ζ, X i ζ-Y i ζ ∂μ) (ENNReal.ofReal p) μ
    calc
      _ ≤ ENNReal.ofReal (w i)*ENNReal.ofReal (2*C) :=
        he.trans_le (mul_le_mul_of_nonneg_left hc' (zero_le : (0:ℝ≥0∞) ≤ _))
      _ = _ := by rw [← ENNReal.ofReal_mul (hw i)]; congr 1; ring
  have hs : eLpNorm (∑ i, Z i) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (2*C*(∑ i, w i)) := by
    apply (eLpNorm_sum_le hpE).trans
    calc
      _ ≤ ∑ i, ENNReal.ofReal (2*C*w i) := Finset.sum_le_sum fun i _ => hZ i
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (by positivity) (hw i)),Finset.mul_sum]
  have he : (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) =
      (fun ω => ∑ i, w i*(Y i ω-∫ ζ, Y i ζ ∂μ))+(∑ i, Z i) := by
    funext ω
    simp only [Pi.add_apply,Finset.sum_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [Z]
    rw [integral_sub (hX i) (hY i)]
    ring
  rw [he]
  exact (eLpNorm_add_le hpE).trans (add_le_add le_rfl hs)

end
end ASDExplicitGamma.Inverse
