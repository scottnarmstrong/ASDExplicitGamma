module

public import ASDExplicitGamma.Native.GenericSourceHolderMinima

/-! The inverse-trace part of the source finite-Holder minimum. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Coarse trace duality gives the sharp finite scalar inverse-trace bound. -/
theorem native_source_inverse_trace_scalar (x y : ℝ)
    (hprod : 4 ≤ x*y) (htrace : 0 ≤ x+y-4) :
    y ≤ 2+(x+y-4)+Real.sqrt (2*(x+y-4)) := by
  let T := x+y-4
  have hT : 0 ≤ T := htrace
  have hsum : x+y=T+4 := by dsimp only [T]; ring
  have hrad : 0 ≤ T*(T+8) := mul_nonneg hT (by positivity)
  have hsq : (y-x)^2 ≤ T*(T+8) := by dsimp only [T]; nlinarith only [hprod]
  have hd : |y-x| ≤ Real.sqrt (T*(T+8)) := by
    apply (Real.le_sqrt (abs_nonneg _) hrad).2
    rwa [sq_abs]
  have hs : (Real.sqrt (2*T))^2 = 2*T := Real.sq_sqrt (by positivity)
  have hr : Real.sqrt (T*(T+8)) ≤ T+2*Real.sqrt (2*T) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith only [hs,mul_nonneg hT (Real.sqrt_nonneg (2*T))]
  have hd' := (le_abs_self (y-x)).trans hd
  change y ≤ 2+T+Real.sqrt (2*T)
  linarith only [hd',hr,hsum]

/-- The L20 norm of the square-root defect is controlled by the square root
of its actual L20 cap, using probability-law monotonicity at order ten. -/
theorem native_source_sqrt_L20 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [hprob : IsProbabilityMeasure μ] (T : Ω → ℝ)
    (hT : AEStronglyMeasurable T μ) (hT0 : ∀ᵐ ω ∂μ, 0 ≤ T ω)
    (A : ℝ≥0∞) (hcap : eLpNorm' T 20 μ ≤ A) :
    eLpNorm' (fun ω => Real.sqrt (T ω)) 20 μ ≤ A^(1/2:ℝ) := by
  have heq : (fun ω => Real.sqrt (T ω)) =ᵐ[μ] (fun ω => ‖T ω‖^(1/2:ℝ)) := by
    filter_upwards [hT0] with ω hω
    rw [Real.norm_of_nonneg hω,Real.sqrt_eq_rpow]
  rw [eLpNorm'_congr_ae heq,eLpNorm'_norm_rpow T 20 (1/2) (by norm_num)]
  norm_num only [show (20:ℝ)*(1/2)=10 by norm_num]
  exact ENNReal.rpow_le_rpow
    ((eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num : (0:ℝ)<10) (by norm_num : (10:ℝ)≤20) μ hT).trans hcap)
    (by norm_num)

/-- The scalar inverse-trace bound passes to its genuine L20 norm. Together
with the local-bank bound 2b, this is the d-minimum. -/
theorem native_source_inverse_trace_L20 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [hprob : IsProbabilityMeasure μ] (T D : Ω → ℝ)
    (hT : AEStronglyMeasurable T μ) (hT0 : ∀ᵐ ω ∂μ, 0 ≤ T ω)
    (hD0 : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    (hD : ∀ᵐ ω ∂μ, D ω ≤ 2+T ω+Real.sqrt (2*T ω))
    (A : ℝ≥0∞) (hcap : eLpNorm' T 20 μ ≤ A) :
    eLpNorm' D 20 μ ≤ ENNReal.ofReal 2+A+ENNReal.ofReal (Real.sqrt 2)*A^(1/2:ℝ) := by
  have hs := native_source_sqrt_L20 μ T hT hT0 A hcap
  have hm : AEStronglyMeasurable (fun ω => Real.sqrt (T ω)) μ := Real.continuous_sqrt.comp_aestronglyMeasurable hT
  have hdom : eLpNorm' D 20 μ ≤
      eLpNorm' (fun ω => 2+T ω+Real.sqrt 2*Real.sqrt (T ω)) 20 μ := by
    apply eLpNorm'_mono_ae (by norm_num : (0:ℝ)≤20)
    filter_upwards [hD0,hT0,hD] with ω hDω hTω hω
    rw [Real.norm_of_nonneg hDω,Real.norm_of_nonneg (by positivity : (0:ℝ)≤2+T ω+Real.sqrt 2*Real.sqrt (T ω))]
    simpa only [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] using hω
  have hadd := eLpNorm'_add_le (f := fun ω => 2+T ω)
    (g := fun ω => Real.sqrt 2*Real.sqrt (T ω)) (aestronglyMeasurable_const.add hT)
    (hm.const_mul _) (by norm_num : (1:ℝ)≤20)
  have hbase := eLpNorm'_add_le (f := fun _ : Ω => (2:ℝ)) (g := T)
    aestronglyMeasurable_const hT (by norm_num : (1:ℝ)≤20)
  rw [eLpNorm'_const_of_isProbabilityMeasure 2 (by norm_num),
    Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤2)] at hbase
  have hscale : eLpNorm' (fun ω => Real.sqrt 2*Real.sqrt (T ω)) 20 μ =
      ENNReal.ofReal (Real.sqrt 2)*eLpNorm' (fun ω => Real.sqrt (T ω)) 20 μ := by
    exact (eLpNorm'_const_smul (Real.sqrt 2) (by norm_num : (0:ℝ)<20)).trans
      (by rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _)])
  rw [hscale] at hadd
  exact (hdom.trans hadd).trans (add_le_add (hbase.trans (add_le_add le_rfl hcap))
    (mul_le_mul' le_rfl hs))

end
end ASDExplicitGamma.Native
