module

public import ASDExplicitGamma.Cold.PlateauCutoff

/-! # Moment computations from the exact spatial plateau tail profile -/

@[expose] public section

open MeasureTheory Set

namespace ASDExplicitGamma.Cold

/-- The exact first moment for any measure with the source plateau tail profile. -/
theorem integral_plateau_profile {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) (hnn : 0 ≤ᵐ[μ] f) (hb : f ≤ᵐ[μ] (fun _ => (12 / 7 : ℝ)))
    (htail : ∀ s : ℝ, 0 ≤ s → s ≤ 12 / 7 → μ.real {x | s ≤ f x} = (1 - 7 * s / 24) ^ 2) :
    ∫ x, f x ∂μ = 1 := by
  rw [hf.integral_eq_integral_Ioc_meas_le hnn hb]
  calc
    _ = ∫ s in Ioc (0 : ℝ) (12 / 7), (1 - 7 * s / 24) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      exact htail s hs.1.le hs.2
    _ = ∫ s in (0 : ℝ)..(12 / 7), (1 - 7 * s / 24) ^ 2 :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = 1 := by
      have heq : (fun s : ℝ => (1 - 7 * s / 24) ^ 2) =
          (fun s => 1 - (7 / 12 : ℝ) * s + (49 / 576 : ℝ) * s ^ 2) := by
        funext s; ring
      rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, integral_id,
        integral_pow]
      · norm_num
      all_goals apply Continuous.intervalIntegrable; fun_prop


/-- The exact second moment for the same spatial profile. -/
theorem integral_plateau_profile_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hnn : 0 ≤ᵐ[μ] f)
    (hb : f ≤ᵐ[μ] (fun _ => (12 / 7 : ℝ)))
    (htail : ∀ s : ℝ, 0 ≤ s → s ≤ 12 / 7 → μ.real {x | s ≤ f x} = (1 - 7 * s / 24) ^ 2) :
    ∫ x, f x ^ 2 ∂μ = 66 / 49 := by
  have hsq : (fun x => f x ^ 2) ≤ᵐ[μ] (fun _ => (12 / 7 : ℝ) ^ 2) := by
    filter_upwards [hnn, hb] with x hx hxM
    exact pow_le_pow_left₀ hx hxM 2
  have hsquare (s : ℝ) (hs : 0 ≤ s) (hsM : s ≤ (12 / 7 : ℝ) ^ 2) :
      μ.real {x | s ≤ f x ^ 2} = (1 - 7 * Real.sqrt s / 24) ^ 2 := by
    have hroot : Real.sqrt s ≤ 12 / 7 := (Real.sqrt_le_iff).mpr ⟨by norm_num, hsM⟩
    rw [← htail (Real.sqrt s) (Real.sqrt_nonneg s) hroot]
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hnn] with x hx
    apply propext
    exact ((Real.sqrt_le_iff).trans (and_iff_right hx)).symm
  rw [hf2.integral_eq_integral_Ioc_meas_le (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hsq]
  calc
    _ = ∫ s in Ioc (0 : ℝ) ((12 / 7 : ℝ) ^ 2), (1 - 7 * Real.sqrt s / 24) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      exact hsquare s hs.1.le hs.2
    _ = ∫ s in (0 : ℝ)..((12 / 7 : ℝ) ^ 2),
        (1 - (7 / 12 : ℝ) * Real.sqrt s + (49 / 576 : ℝ) * s) := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      nlinarith only [Real.sq_sqrt hs.1.le]
    _ = 66 / 49 := by
      rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, integral_sqrt_plateau_endpoint, integral_id]
      · norm_num
      all_goals apply Continuous.intervalIntegrable; fun_prop


end ASDExplicitGamma.Cold
