module

public import ASDExplicitGamma.Cold.PlateauWeights
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Summable depth envelopes for the actual plateau series -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold

/-- The general geometric weight envelope is summable, including the exceptional first weight. -/
theorem summable_plateau_weighted {b : ℝ} (hb : ‖b/9‖ < 1) :
    Summable (fun k : ℕ => plateauEvenWeight k*b^(k+1)) := by
  apply (summable_nat_add_iff 1).mp
  have hg := (summable_geometric_of_norm_lt_one hb).mul_left ((28:ℝ)*(b/9)^2)
  convert hg using 1
  funext k
  rw [plateauEvenWeight,ite_eq_right (by omega)]
  have he : (1/9:ℝ)^(k+1+1)*b^(k+1+1) = (b/9)^(k+1+1) := by
    rw [← mul_pow]
    congr 1
    ring
  rw [mul_assoc,he,show k+1+1 = 2+k by omega,pow_add]
  ring

/-- The source real depth factor equals the corresponding integer power of sqrt three. -/
theorem plateau_even_depth_factor (k : ℕ) :
    (3:ℝ)^(((2*(k+1):ℕ):ℝ)/4) = (Real.sqrt 3)^(k+1) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-- The source sqrt-three weighted plateau series is absolutely convergent. -/
theorem summable_plateauEvenWeight_sqrtThree :
    Summable (fun k : ℕ => plateauEvenWeight k*(Real.sqrt 3)^(k+1)) := by
  apply summable_plateau_weighted
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h := Numerics.Cold.sqrtThree_lt_twentySixOverFifteen
  linarith only [h]

/-- The all-depth pathwise history envelope is summable against the plateau weights. -/
theorem summable_plateau_history_envelope :
    Summable (fun k : ℕ => plateauEvenWeight k*(8+6*(3:ℝ)^(((2*(k+1):ℕ):ℝ)/4))) := by
  simp_rw [plateau_even_depth_factor]
  convert (summable_plateauEvenWeight.mul_left 8).add
    (summable_plateauEvenWeight_sqrtThree.mul_left 6) using 1
  funext k
  ring

end ASDExplicitGamma.Cold
