module

public import ASDExplicitGamma.Scalar.InverseHistoryBlocks

/-! The literal extended source formula for TR-INV-HISTORY. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational
open scoped ENNReal

/-- Integer depth powers of the discount have the exact source real-power exponent. -/
theorem inverse_history_discount_power (d : ℕ) : inverseHistoryDiscount^d=(3:ℝ)^(-(d:ℝ)/4) := by
  unfold inverseHistoryDiscount
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  congr 1
  ring

end ASDExplicitGamma.Scalar
