module

public import ASDExplicitGamma.Inverse.PositiveSplit
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Moment conversion used by the positive inverse-bank splits. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory

open scoped ENNReal

theorem bank_ennreal_affine_Lp_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p C A : ℝ≥0∞) (H E : Ω → ℝ≥0∞)
    (hCfin : C ≠ ∞) (hAfin : A ≠ ∞)
    (hH : Measurable H) (hE : Measurable E) (hp : 1 ≤ p) :
    eLpNorm (fun ω => (H ω * A + E ω) * C) p μ ≤
      C * (A * eLpNorm H p μ + eLpNorm E p μ) := by
  let X : Ω → ℝ≥0∞ := fun ω => H ω * A + E ω
  let X₁ : Ω → ℝ≥0∞ := fun ω => H ω * A
  have hH₁ : Measurable X₁ :=
    (ENNReal.continuous_mul_const hAfin).measurable.comp hH
  have hX : Measurable X := hH₁.add hE
  have hX₁ : Measurable X₁ := hH₁
  have hOuter : Measurable (fun ω => X ω * C) :=
    (ENNReal.continuous_mul_const hCfin).measurable.comp hX
  have houter : eLpNorm (fun ω => X ω * C) p μ ≤ C * eLpNorm X p μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
      (hOuter.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _ => by simp [enorm_eq_self, mul_comm])
  have hsum : eLpNorm X p μ ≤ eLpNorm X₁ p μ + eLpNorm E p μ := by
    exact eLpNorm_add_le hp
  have hscale : eLpNorm X₁ p μ ≤ A * eLpNorm H p μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
      (hX₁.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _ => by simp [X₁, enorm_eq_self, mul_comm])
  calc
    _ ≤ C * eLpNorm X p μ := houter
    _ ≤ C * (eLpNorm X₁ p μ + eLpNorm E p μ) :=
      mul_le_mul_of_nonneg_left hsum (bot_le)
    _ = C * eLpNorm X₁ p μ + C * eLpNorm E p μ := by rw [mul_add]
    _ ≤ C * (A * eLpNorm H p μ) + C * eLpNorm E p μ :=
      add_le_add_left (mul_le_mul_of_nonneg_left hscale (bot_le)) _
    _ = C * (A * eLpNorm H p μ + eLpNorm E p μ) := by rw [mul_add]

theorem bank_L128_cap_of_L256_excess {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (A e : ℝ) (hA : 0 ≤ A) (_he : 0 ≤ e)
    (hExcess : eLpNorm (fun ω => max 0 (Y ω - A)) 256 μ ≤ ENNReal.ofReal e) :
    eLpNorm Y 128 μ ≤ ENNReal.ofReal A + ENNReal.ofReal e := by
  let X : Ω → ℝ := fun ω => max 0 (Y ω - A)
  have hX : Measurable X := measurable_const.max (hY.sub_const A)
  have hY256 : eLpNorm Y 256 μ ≤ ENNReal.ofReal A + ENNReal.ofReal e := by
    calc
      _ ≤ eLpNorm ((fun _ : Ω => A) + X) 256 μ := by
        apply eLpNorm_mono_ae_real hY.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω)]
          change Y ω ≤ A + max 0 (Y ω - A)
          linarith only [le_max_right (0 : ℝ) (Y ω - A)]
      _ ≤ eLpNorm (fun _ : Ω => A) 256 μ + eLpNorm X 256 μ :=
        eLpNorm_add_le (by norm_num)
      _ = ENNReal.ofReal A + eLpNorm X 256 μ := by
        rw [eLpNorm_const' A (by norm_num) (by norm_num), Real.enorm_of_nonneg hA]
        simp only [measure_univ, ENNReal.one_rpow, mul_one]
      _ ≤ ENNReal.ofReal A + ENNReal.ofReal e := by
        simpa only [X] using add_le_add_right hExcess (ENNReal.ofReal A)
  have hmono : eLpNorm Y 128 μ ≤ eLpNorm Y 256 μ := by
    simpa only [measure_univ, ENNReal.one_rpow, mul_one] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (f := Y) (μ := μ) (p := 128) (q := 256)
        (by norm_num) hY.aestronglyMeasurable)
  exact hmono.trans hY256

end ASDExplicitGamma.Inverse
