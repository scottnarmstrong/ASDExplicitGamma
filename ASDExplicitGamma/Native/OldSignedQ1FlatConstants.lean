module

public import ASDExplicitGamma.Native.BoundaryChargeFlatConstants

/-! Exact rational outward constants used by the frozen q1 setup. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Triadic
noncomputable section

/-- The actual weak Poincaré constant fits the panel's .440 coefficient. -/
theorem old_signed_q1_planarC0_le : planarC0≤(11/25:ℝ) := by
  have hs : Real.sqrt 3≤(26/15:ℝ) := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
    nlinarith only [hh,Real.sqrt_nonneg (3:ℝ)]
  have hp : (157/50:ℝ)≤Real.pi := by linarith only [Real.pi_gt_d2]
  have hp2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤157/50) hp 2
  have hd : (9-26/15:ℝ)*(157/50)^2≤(9-Real.sqrt 3)*Real.pi^2 :=
    mul_le_mul (sub_le_sub_left hs 9) hp2 (by norm_num) (by linarith only [hs])
  have hd0 : 0<(9-Real.sqrt 3)*Real.pi^2 :=
    lt_of_lt_of_le (by norm_num : (0:ℝ)<(9-26/15)*(157/50)^2) hd
  have hn : 8*Real.sqrt 3≤(11/25:ℝ)^2*((9-Real.sqrt 3)*Real.pi^2) := by
    calc
      _ ≤ 8*(26/15:ℝ) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ ≤ (11/25:ℝ)^2*((9-26/15)*(157/50)^2) := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (sq_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤11/25)).mp
  change planarC0^2≤(11/25:ℝ)^2
  rw [planarC0_sq]
  exact (div_le_iff₀ hd0).mpr hn

/-- The actual derivative Poincaré coefficient fits the panel's .637. -/
theorem old_signed_q1_two_div_pi_le : 2/Real.pi≤(637/1000:ℝ) := by
  apply (div_le_iff₀ Real.pi_pos).mpr
  have hp : (157/50:ℝ)≤Real.pi := by linarith only [Real.pi_gt_d2]
  have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤637/1000)
  linarith only [hh]

end
end ASDExplicitGamma.Native
