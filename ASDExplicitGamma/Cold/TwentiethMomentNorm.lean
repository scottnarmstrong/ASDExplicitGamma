module

public import ASDExplicitGamma.Cold.LpMonotonicity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exact conversion between the L20 cap and twentieth-moment integrals -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Cold

/-- The twentieth power of the actual real L20 norm is the even moment integral. -/
theorem cold_lpNorm_twenty_pow {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 20 ℙ) :
    (lpNorm X 20 ℙ)^20 = ∫ ω, X ω^20 ∂ℙ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hX.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
  have he : (fun ω => ‖X ω‖^20) = (fun ω => X ω^20) := by
    funext ω
    simp only [Real.norm_eq_abs,show (20:ℕ)=2*10 by norm_num,pow_mul,sq_abs]
  rw [he,← Real.rpow_mul_natCast (integral_nonneg (fun ω => by positivity))]
  norm_num

/-- A finite L20 cap yields the exact twentieth-moment cap used by P5/P6. -/
theorem cold_integral_twentieth_le {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {X : Ω → ℝ} {M : ℝ} (hX : MemLp X 20 ℙ) (hcap : lpNorm X 20 ℙ ≤ M) :
    (∫ ω, X ω^20 ∂ℙ) ≤ M^20 := by
  rw [← cold_lpNorm_twenty_pow hX]
  exact pow_le_pow_left₀ lpNorm_nonneg hcap 20

end ASDExplicitGamma.Cold
