module

public import ASDExplicitGamma.Native.ParentWeakFieldSelected
public import ASDExplicitGamma.Native.ParentWeakFieldSlopeComparison

/-! The exact weak-field comparison consumed by the actual parent generator. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Scalar Algsuperdiff.Section3
noncomputable section

/-- Every physical primitive weak allowance, including the larger correlated
reserve, is below the ACTUAL selected unrounded parent weak field. -/
theorem parent_weak_panel_comparison (j : Fin 16) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    (23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero (j.val+1)+(2/10^12:ℝ) ≤
      (parentRowFields j).getD 15 0+(parentRowFields j).getD 12 0*t := by
  have hsl := (parent_weak_field_primitive_le_value (j.val+1)).trans_eq
    (parent_weak_field_slope_eq j).symm
  have hini : (23/100:ℝ)+(2/10^12:ℝ) ≤ (parentRowFields j).getD 15 0 :=
    (by norm_num : (23/100:ℝ)+(2/10^12:ℝ) ≤ 231/1000).trans (parent_weak_field_initial_lower j)
  calc
    _ = ((23/100:ℝ)+(2/10^12:ℝ))+parentBoundaryWeakMeanSlope gammaZero (j.val+1)*t := by ring
    _ ≤ _ := add_le_add hini (mul_le_mul_of_nonneg_right hsl ht.1)

end
end ASDExplicitGamma.Native
