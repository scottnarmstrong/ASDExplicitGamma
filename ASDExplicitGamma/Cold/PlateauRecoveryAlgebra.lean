module

public import ASDExplicitGamma.Cold.PlateauOnSquareMoments
public import ASDExplicitGamma.Cold.SquareVectorEnergy

/-! # Source Young inequality and the corrected cutoff-recovery algebra -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The main mean in the expanded cutoff-recovery bound is the terminal mean. -/
theorem plateau_recovery_lower_bound {c e μsmall μlarge : ℝ} 
    (h : (1-c)*(2*(7/8)*μsmall) - (1/c-1)*(12/7)*(2*(μsmall-μlarge)) ≤ e) :
    2*(1-c)*(7/8)*μlarge -
      2*((1/c-1)*(12/7)-(1-c)*(7/8))*(μsmall-μlarge) ≤ e := by
  convert h using 1
  ring

/-- The corrected source recovery constants follow by division by the positive main coefficient. -/
theorem plateau_recovery_constants {c e μsmall μlarge : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h : 2*(1-c)*(7/8)*μlarge -
      2*((1/c-1)*(12/7)-(1-c)*(7/8))*(μsmall-μlarge) ≤ e) :
    μlarge ≤ (4/(7*(1-c)))*e + (96/(49*c)-1)*(μsmall-μlarge) := by
  have hp : 0 < 7*(1-c) := by positivity
  apply (mul_le_mul_iff_of_pos_left hp).mp
  have heq : (7*(1-c))*((4/(7*(1-c)))*e + (96/(49*c)-1)*(μsmall-μlarge)) =
      4*e + 4*(2*((1/c-1)*(12/7)-(1-c)*(7/8)))*(μsmall-μlarge) := by
    field_simp [hc.ne', (ne_of_gt (by linarith : 0 < 1-c))]
    ring
  rw [heq]
  linarith only [h]

end ASDExplicitGamma.Cold
