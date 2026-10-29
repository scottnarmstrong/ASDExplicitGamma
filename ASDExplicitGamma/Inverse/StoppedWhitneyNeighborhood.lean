module

public import ASDExplicitGamma.Inverse.StoppedWhitneySeparation

/-! A stopped lifted chain cannot have a closure-touching neighborhood two
macro-layers wide. All endpoint widths are paid before the contradiction. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- A fine descendant's radius is no larger than its actual parent's. -/
theorem descendant_radius_le {A V : TriadicCube 2} {r : ℕ}
    (hV : V ∈ descendantsAtDepth A r) : cubeRadius V ≤ cubeRadius A := by
  rw [cubeRadius_eq_zpow_div_two,cubeRadius_eq_zpow_div_two,
    scale_eq_sub_of_mem_descendantsAtDepth hV]
  exact div_le_div_of_nonneg_right
    (zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 3) (by omega)) (by norm_num)

end
end ASDExplicitGamma.Inverse
