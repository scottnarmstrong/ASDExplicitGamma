module

public import ASDExplicitGamma.Native.OldSignedFull64HistoryTransport

/-! A certified affine envelope for the actual evolving OLD maximum history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Exact fourth-power certification of the retained initial strong term. -/
theorem old_signed_initial_history_rational :
    (coldHistoryBeta^5)⁻¹*(2379/2500:ℝ)≤217/100 := by
  have hb : (coldHistoryBeta^5)^4=(1/27:ℝ) := by
    rw [←pow_mul,cold_native_beta_power]
    norm_num [Real.rpow_neg,Real.rpow_natCast]
  have hx : 0≤(coldHistoryBeta^5)⁻¹*(2379/2500:ℝ) := by
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg coldHistoryBeta_pos.le _)) (by norm_num)
  apply (pow_le_pow_iff_left₀ hx (by norm_num) (by norm_num : (4:ℕ)≠0)).mp
  rw [mul_pow,inv_pow,hb]
  norm_num

end
end ASDExplicitGamma.Native
