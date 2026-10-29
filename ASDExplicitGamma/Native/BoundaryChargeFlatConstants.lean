module

public import ASDExplicitGamma.Triadic.PlanarConstants
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.Linarith

/-! The sharper positive-norm coefficient used by the boundary-fixed OLD
source, separately from the main outward boundary coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Triadic
noncomputable section

/-- The OLD coefficient .304 is a certified upper bound for the actual
planar positive-norm Poincare constant. -/
theorem native_boundary_planarC1_le : planarC1 ≤ (304/1000:ℝ) := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsq : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 3 ≤ (26/15:ℝ) := by nlinarith only [hsq,hs0]
  have hp : (157/50:ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d2]
  have hp2 : (157/50:ℝ)^2 ≤ Real.pi^2 :=
    pow_le_pow_left₀ (by norm_num) hp 2
  have hf : (1-26/135:ℝ) ≤ 1-Real.sqrt 3/9 := by linarith only [hs]
  have hd : 0 < Real.pi^2*(1-Real.sqrt 3/9) :=
    mul_pos (pow_pos Real.pi_pos _) (lt_of_lt_of_le (by norm_num : (0:ℝ)<1-26/135) hf)
  have hdlo : (157/50:ℝ)^2*(1-26/135) ≤ Real.pi^2*(1-Real.sqrt 3/9) :=
    mul_le_mul hp2 hf (by norm_num) (sq_nonneg Real.pi)
  have hnum : Real.sqrt 3-1 ≤ (304/1000:ℝ)^2*(Real.pi^2*(1-Real.sqrt 3/9)) := by
    calc
      _ ≤ (26/15:ℝ)-1 := sub_le_sub_right hs 1
      _ ≤ (304/1000:ℝ)^2*((157/50)^2*(1-26/135)) := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hdlo (sq_nonneg _)
  have hcap : planarC1^2 ≤ (304/1000:ℝ)^2 := by
    rw [planarC1_sq]
    exact (div_le_iff₀ hd).mpr hnum
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hcap

end
end ASDExplicitGamma.Native
