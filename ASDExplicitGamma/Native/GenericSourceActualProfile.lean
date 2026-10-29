module

public import ASDExplicitGamma.Native.GenericSourceRefinedNorms
public import ASDExplicitGamma.Inverse.SourceRefinedBudget
public import ASDExplicitGamma.Native.GenericSourceRawTailProfile

/-! The literal finite source profile, now bounding the actual partial
laws after all four heat refinements. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- The true-power clock is below its finite rational source majorant. -/
theorem native_source_true_variance_le_generic (gamma : ℝ) (height : ℕ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ 17/50000) (hh : height ≤ 1334) :
    nativeSourceRawShellVarianceCap gamma height ≤ nativeSourceGenericVarianceCap gamma height := by
  exact mul_le_mul_of_nonneg_left (native_source_E_ge_three_power gamma height hg0 hg hh)
    (mul_nonneg (by norm_num : (0:ℝ)≤9/2) hg0)

end
end ASDExplicitGamma.Native
