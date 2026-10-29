module

public import ASDExplicitGamma.Gaussian.RioTwentyMoment
public import Mathlib.Probability.Independence.Integration

/-! # Sharp L20 one-step inequality and its independent centered specialization -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Gaussian

/-- The squared L20 norm is exactly the one-tenth power of the even twentieth moment. -/
theorem rio_lpNorm_twenty_sq {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 20 ℙ) :
    (lpNorm X 20 ℙ)^2 = (∫ ω, X ω^20 ∂ℙ)^((1:ℝ)/10) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hX.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
  have he : (fun ω => ‖X ω‖^20) = (fun ω => X ω^20) := by
    funext ω
    simp only [Real.norm_eq_abs,show (20:ℕ)=2*10 by norm_num,pow_mul,sq_abs]
  rw [he,← Real.rpow_mul_natCast (integral_nonneg (fun ω => by positivity))]
  norm_num

/-- The sharp twentieth-norm inequality from exact mixed-moment cancellation. -/
theorem rio_lpNorm_twenty_one_step {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] {S X : Ω → ℝ} (hS : MemLp S 20 ℙ) (hX : MemLp X 20 ℙ)
    (horth : (∫ ω, S ω^19*X ω ∂ℙ) = 0) :
    (lpNorm (fun ω => S ω+X ω) 20 ℙ)^2 ≤ (lpNorm S 20 ℙ)^2+19*(lpNorm X 20 ℙ)^2 := by
  have hSX : MemLp (fun ω => S ω+X ω) 20 ℙ := hS.add hX
  rw [rio_lpNorm_twenty_sq hSX,rio_lpNorm_twenty_sq hS,rio_lpNorm_twenty_sq hX]
  exact rio_twentieth_moment_one_step hS hX horth

/-- The cold Rio one-step estimate for independent centered real L20 variables. -/
theorem rio_lpNorm_twenty_independent {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] {S X : Ω → ℝ} (hS : MemLp S 20 ℙ) (hX : MemLp X 20 ℙ)
    (hIndep : ProbabilityTheory.IndepFun S X ℙ) (hCenter : (∫ ω, X ω ∂ℙ) = 0) :
    (lpNorm (fun ω => S ω+X ω) 20 ℙ)^2 ≤ (lpNorm S 20 ℙ)^2+19*(lpNorm X 20 ℙ)^2 := by
  apply rio_lpNorm_twenty_one_step hS hX
  have hi := hIndep.comp (measurable_id.pow_const 19) measurable_id
  have h := hi.integral_mul_eq_mul_integral (hS.aestronglyMeasurable.pow 19) hX.aestronglyMeasurable
  change (∫ ω, S ω^19*X ω ∂ℙ) = (∫ ω, S ω^19 ∂ℙ)*(∫ ω, X ω ∂ℙ) at h
  rw [hCenter,mul_zero] at h
  exact h

end ASDExplicitGamma.Gaussian
