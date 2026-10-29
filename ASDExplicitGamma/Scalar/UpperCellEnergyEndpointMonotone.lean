module

public import ASDExplicitGamma.Scalar.UpperCellEnergyEndpointProfiles

/-! Termwise endpoint comparison of the positive UPPER error profiles. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
noncomputable section

/-- The complete future history is nonnegative and endpoint dominated on
the physical block rectangle. No optimized-root comparison is used. -/
theorem upper_cell_history_profile_bounds (gamma block : ℝ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hb0 : 0 ≤ block) (hb : block ≤ 17/50) :
    0 ≤ upperCellHistoryProfile gamma block ∧
      upperCellHistoryProfile gamma block ≤ upperCellHistoryProfile gammaZero (17/50) := by
  let A := fun g b : ℝ => 4*((1130469/10^6:ℝ)*(1009309/500000)+
    16684*((1130469/10^6:ℝ)*(b+15*g)+g*(838143/200000))+
    g*5899542*(1130469/10^6:ℝ))
  let D := fun g b : ℝ => 1-(11/10:ℝ)*(2*b+60*g)
  have hA0 : 0 ≤ A gamma block := by dsimp only [A]; positivity
  have hA : A gamma block ≤ A gammaZero (17/50) := by
    change gamma ≤ 17/50000 at hg
    dsimp [A, gammaZero]
    nlinarith only [hg,hb]
  have hD : D gammaZero (17/50) ≤ D gamma block := by
    change gamma ≤ 17/50000 at hg
    dsimp [D,gammaZero]
    linarith only [hg,hb]
  have hD0 : 0 < D gamma block := upper_cell_profile_denominator_pos _ _ hg hb
  have hDe : 0 < D gammaZero (17/50) := by norm_num [D,gammaZero]
  change 0 ≤ A gamma block/D gamma block ∧
    A gamma block/D gamma block ≤ A gammaZero (17/50)/D gammaZero (17/50)
  refine ⟨div_nonneg hA0 hD0.le, (div_le_div_iff₀ hD0 hDe).mpr ?_⟩
  exact (mul_le_mul_of_nonneg_right hA hDe.le).trans
    (mul_le_mul_of_nonneg_left hD (hA0.trans hA))

/-- Nonnegativity and monotonicity of the physical f profile. -/
theorem upper_cell_f_profile_bounds (gamma : ℝ) (hg : gamma ≤ gammaZero) :
    0 ≤ upperCellFProfile gamma ∧ upperCellFProfile gamma ≤ upperCellFProfile gammaZero := by
  constructor
  · unfold upperCellFProfile; positivity
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (by norm_num)) (by norm_num)

/-- Compare the complete cubic sensitivity term before adding other errors. -/
theorem upper_cell_sensitivity_profile_bounds (gamma : ℝ) (hg : gamma ≤ gammaZero) :
    0 ≤ upperCellSensitivityProfile gamma ∧
      upperCellSensitivityProfile gamma ≤ upperCellSensitivityProfile gammaZero := by
  have hf := upper_cell_f_profile_bounds gamma hg
  have hf0 := hf.1
  have h2 := pow_le_pow_left₀ hf.1 hf.2 2
  have h3 := pow_le_pow_left₀ hf.1 hf.2 3
  constructor
  · unfold upperCellSensitivityProfile
    positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (add_le_add hf.2 (mul_le_mul_of_nonneg_left h2 (by norm_num)))
      (mul_le_mul_of_nonneg_left h3 (by norm_num))

/-- Compare the residual with both its positive gamma factor and full history. -/
theorem upper_cell_residual_profile_bounds (gamma block : ℝ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hb0 : 0 ≤ block) (hb : block ≤ 17/50) :
    0 ≤ upperCellResidualProfile gamma block ∧
      upperCellResidualProfile gamma block ≤ upperCellResidualProfile gammaZero (17/50) := by
  have hh := upper_cell_history_profile_bounds gamma block hg0 hg hb0 hb
  have hh0 := hh.1
  constructor
  · unfold upperCellResidualProfile; positivity
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hh.2 (by norm_num)) hg hg0
      (mul_nonneg (by norm_num) (hh.1.trans hh.2))

/-- Every positive term, including the correlated square-root cross term,
is bounded by its endpoint counterpart. -/
theorem upper_cell_error_profile_le (gamma block : ℝ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hb0 : 0 ≤ block) (hb : block ≤ 17/50) :
    upperCellErrorProfile gamma block ≤ upperCellErrorProfile gammaZero (17/50) := by
  have hs := (upper_cell_sensitivity_profile_bounds gamma hg).2
  have hr := (upper_cell_residual_profile_bounds gamma block hg0 hg hb0 hb).2
  have hc := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ)≤2)))
    (by norm_num : (0:ℝ)≤2)
  have ht := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤4))
    (by norm_num : (0:ℝ)≤3^28)
  exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl hs) hc) hr) ht

end
end ASDExplicitGamma.Scalar
