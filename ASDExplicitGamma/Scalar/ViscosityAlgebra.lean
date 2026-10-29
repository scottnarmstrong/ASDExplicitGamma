module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The fixed-law viscosity comparison has viscosity-independent admissible
states and cost nu P+Q/nu with P,Q≥0. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

/-- Exact comparison of the doubled pointwise costs with a fixed skew component. -/
theorem viscosity_cost_comparison (nu r P Q : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (hr1 : r ≤ 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    r*(nu*P+Q/nu) ≤ r*nu*P+Q/(r*nu) ∧
      r*nu*P+Q/(r*nu) ≤ r⁻¹*(nu*P+Q/nu) := by
  have hr2 : r^2 ≤ 1 := by nlinarith only [hr,hr1]
  have hden : 0 < r*nu := mul_pos hr hnu
  have hp := mul_nonneg (sub_nonneg.mpr hr2) hP
  have hq := mul_nonneg (sub_nonneg.mpr hr2) hQ
  constructor
  · apply (mul_le_mul_iff_of_pos_right hden).mp
    field_simp
    nlinarith only [hq]
  · apply (mul_le_mul_iff_of_pos_right hden).mp
    field_simp
    nlinarith only [hp,sq_nonneg nu]

end ASDExplicitGamma.Scalar
