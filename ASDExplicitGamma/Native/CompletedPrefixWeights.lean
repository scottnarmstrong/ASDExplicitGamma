module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import ASDExplicitGamma.Native.GenericSourceWeightedRows
public import ASDExplicitGamma.Native.GenericSourceRawTailProfile

/-! The actual and outward weights in the completed-prefix identity.
Both the retained gain and the unreplaced complete source weights are kept. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The coarse source alpha brackets enclose the physical fourth root. -/
theorem native_completed_prefix_alpha_bracket :
    nativeSourceAlphaMinus ≤ (1/3:ℝ)^(1/4:ℝ) ∧
      (1/3:ℝ)^(1/4:ℝ) ≤ nativeSourceAlphaPlus := by
  have hl : nativeSourceAlphaMinus ≤ (invAlphaLower:ℝ) := by
    norm_num [nativeSourceAlphaMinus,invAlphaLower]
  have hu : (invAlphaUpper:ℝ) ≤ nativeSourceAlphaPlus := by
    norm_num [nativeSourceAlphaPlus,invAlphaUpper]
  exact ⟨hl.trans inv_alpha_real.1.le,inv_alpha_real.2.le.trans hu⟩

end
end ASDExplicitGamma.Native
