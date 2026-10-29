module

public import ASDExplicitGamma.Gaussian.SpatialKernelSupport
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Integrating localized L² mass over moving physical support boxes -/

@[expose] public section

open MeasureTheory Homogenization Set

namespace ASDExplicitGamma.Gaussian

/-- The local input mass is integrable on any finite spatial measure. -/
theorem integrable_moving_q3SupportBox (L : {l : ℝ // 0 < l})
    (μ : Measure (Vec 2)) [IsFiniteMeasure μ] (u : WhiteNoise) :
    Integrable (fun x => ∫ y in q3SupportBox L x, u y ^ 2) μ := by
  let A : Set (Vec 2 × Vec 2) := {p | dist p.2 p.1 ≤ L.1 / 2}
  let F : Vec 2 × Vec 2 → ℝ := A.indicator (fun p => u p.2 ^ 2)
  have hA : MeasurableSet A := measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const
  have hF : StronglyMeasurable F := ((Lp.stronglyMeasurable u).comp_measurable measurable_snd).pow 2 |>.indicator hA
  have he : (fun x => ∫ y, F (x, y) ∂volume) = fun x => ∫ y in q3SupportBox L x, u y ^ 2 := by
    funext x
    have hrow : (fun y => F (x, y)) = (q3SupportBox L x).indicator (fun y => u y ^ 2) := rfl
    rw [hrow, integral_indicator (measurableSet_q3SupportBox L x)]
  have hm : StronglyMeasurable (fun x => ∫ y in q3SupportBox L x, u y ^ 2) := by
    rw [← he]
    exact hF.integral_prod_right'
  apply Integrable.of_bound hm.aestronglyMeasurable (∫ y, u y ^ 2)
  exact ae_of_all μ fun x => by
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    exact setIntegral_le_integral (Lp.memLp u).integrable_sq (ae_of_all volume fun _ => sq_nonneg _)

/-- The moving support has area L² also after restriction to any finite spatial domain.
This is the Schur/Fubini step in the fine-shell convolution estimate. -/
theorem integral_moving_q3SupportBox_le (L : {l : ℝ // 0 < l})
    (μ : Measure (Vec 2)) [IsFiniteMeasure μ] (hμ : μ ≤ volume) (u : WhiteNoise) :
    (∫ x, ∫ y in q3SupportBox L x, u y ^ 2 ∂volume ∂μ) ≤ L.1 ^ 2 * ‖u‖ ^ 2 := by
  classical
  let A : Set (Vec 2 × Vec 2) := {p | dist p.2 p.1 ≤ L.1 / 2}
  let F : Vec 2 × Vec 2 → ℝ := A.indicator (fun p => u p.2 ^ 2)
  have hA : MeasurableSet A := measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const
  have hF : StronglyMeasurable F := ((Lp.stronglyMeasurable u).comp_measurable measurable_snd).pow 2 |>.indicator hA
  have hF0 (p : Vec 2 × Vec 2) : 0 ≤ F p := indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hcol (y : Vec 2) : (fun x => F (x, y)) = (q3SupportBox L y).indicator (fun _ => u y ^ 2) := by
    funext x
    change (if dist y x ≤ L.1 / 2 then u y ^ 2 else 0) =
      (if x ∈ q3SupportBox L y then u y ^ 2 else 0)
    rw [q3SupportBox, Metric.mem_closedBall, dist_comm]
  have hcolInt (y : Vec 2) : Integrable (fun x => F (x, y)) μ := by
    rw [hcol]
    exact (integrable_const _).indicator (measurableSet_q3SupportBox L y)
  have hvol (y : Vec 2) : μ.real (q3SupportBox L y) ≤ L.1 ^ 2 := by
    have hh := ENNReal.toReal_mono (by rw [volume_q3SupportBox]; exact ENNReal.ofReal_ne_top)
      (show μ (q3SupportBox L y) ≤ volume (q3SupportBox L y) from hμ _)
    simpa only [measureReal_def, volume_q3SupportBox, ENNReal.toReal_ofReal (sq_nonneg L.1)] using hh
  have hcolNorm (y : Vec 2) : (∫ x, ‖F (x, y)‖ ∂μ) ≤ L.1 ^ 2 * u y ^ 2 := by
    simp only [Real.norm_of_nonneg (hF0 _)]
    rw [hcol, integral_indicator_const _ (measurableSet_q3SupportBox L y), smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hvol y) (sq_nonneg _)
  have hinner : Integrable (fun y => ∫ x, ‖F (x, y)‖ ∂μ) volume := by
    apply ((Lp.memLp u).integrable_sq.const_mul (L.1 ^ 2)).mono'
      hF.norm.integral_prod_left'.aestronglyMeasurable
    exact ae_of_all volume fun y => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hcolNorm y
  have hprod : Integrable F (μ.prod volume) :=
    (integrable_prod_iff' hF.aestronglyMeasurable).mpr ⟨ae_of_all volume hcolInt, hinner⟩
  have hrow (x : Vec 2) : (fun y => F (x, y)) = (q3SupportBox L x).indicator (fun y => u y ^ 2) := by
    funext y
    rfl
  calc
    _ = ∫ x, ∫ y, F (x, y) ∂volume ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ fun x => by
        change (∫ y in q3SupportBox L x, u y ^ 2) = ∫ y, F (x, y)
        rw [hrow, integral_indicator (measurableSet_q3SupportBox L x)]
    _ = ∫ y, ∫ x, F (x, y) ∂μ ∂volume := integral_integral_swap hprod
    _ ≤ ∫ y, L.1 ^ 2 * u y ^ 2 ∂volume := by
      apply integral_mono hprod.integral_prod_right ((Lp.memLp u).integrable_sq.const_mul _)
      intro y
      simpa only [Real.norm_of_nonneg (hF0 _)] using hcolNorm y
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [Real.norm_eq_abs, sq_abs] using (l2_norm_sq volume u).symm

end ASDExplicitGamma.Gaussian
