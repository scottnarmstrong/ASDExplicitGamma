module

public import ASDExplicitGamma.Scalar.ReciprocalRegions
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Order.Lattice

/-! The monotone reciprocal weight in the two-region conversion. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory Set intervalIntegral

/-- The source weight min(S^3,Y^3/r^3), with its integer negative power made explicit. -/
noncomputable def reciprocalWeight (S Y r : ℝ) : ℝ := min (S^3) (Y^3*r^(-3:ℤ))

/-- The weight is nonnegative on the positive half-line. -/
theorem reciprocal_weight_nonnegative (S Y r : ℝ) (hS : 0≤S) (hY : 0≤Y) (hr : 0<r) :
    0≤reciprocalWeight S Y r := le_min (by positivity) (by positivity)

/-- The inverse-cube branch is continuous on every interval with positive endpoints. -/
theorem inverse_cube_continuousOn (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    ContinuousOn (fun r : ℝ => r^(-3:ℤ)) (uIcc a b) := by
  exact continuousOn_id.zpow₀ _ (fun r hr => Or.inl (ne_of_gt ((lt_min ha hb).trans_le hr.1)))

/-- The source weight has an honest interval integral, including across the crossover. -/
theorem reciprocal_weight_intervalIntegrable (S Y a b : ℝ) (ha : 0<a) (hb : 0<b) :
    IntervalIntegrable (reciprocalWeight S Y) volume a b :=
  (continuousOn_const.inf (continuousOn_const.mul (inverse_cube_continuousOn a b ha hb))).intervalIntegrable

/-- Exact integral of the inverse-cube branch on a positive interval. -/
theorem integral_inverse_cube (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫ r in a..b,r^(-3:ℤ))=(a^(-2:ℤ)-b^(-2:ℤ))/2 := by
  have hz : (0:ℝ) ∉ uIcc a b := by
    intro h
    exact (lt_min ha hb).not_ge h.1
  rw [integral_zpow (Or.inr ⟨by decide,hz⟩)]
  norm_num
  ring

/-- The source weight is bounded above by its constant branch. -/
theorem integral_reciprocal_weight_le_constant (S Y a b : ℝ)
    (ha : 0<a) (hab : a≤b) :
    (∫ r in a..b,reciprocalWeight S Y r)≤(b-a)*S^3 := by
  have hb : 0<b := ha.trans_le hab
  calc
    _ ≤ ∫ r in a..b,S^3 := integral_mono_on hab
      (reciprocal_weight_intervalIntegrable S Y a b ha hb) intervalIntegrable_const
      (fun r hr => min_le_left _ _)
    _ = _ := by rw [intervalIntegral.integral_const]; rfl

/-- The source weight is bounded above by its inverse-cube branch. -/
theorem integral_reciprocal_weight_le_inverse_cube (S Y a b : ℝ)
    (ha : 0<a) (hab : a≤b) :
    (∫ r in a..b,reciprocalWeight S Y r)≤Y^3*(a^(-2:ℤ)-b^(-2:ℤ))/2 := by
  have hb : 0<b := ha.trans_le hab
  calc
    _ ≤ ∫ r in a..b,Y^3*r^(-3:ℤ) := integral_mono_on hab
      (reciprocal_weight_intervalIntegrable S Y a b ha hb)
      ((continuousOn_const.mul (inverse_cube_continuousOn a b ha hb)).intervalIntegrable)
      (fun r hr => min_le_right _ _)
    _ = _ := by rw [intervalIntegral.integral_const_mul,integral_inverse_cube a b ha hb]; ring

end ASDExplicitGamma.Scalar
