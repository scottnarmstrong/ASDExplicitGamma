module

public import ASDExplicitGamma.Native.GenericSourceInterpolation
public import ASDExplicitGamma.Native.GenericSourceHolderProducts
public import ASDExplicitGamma.Native.HeatVHEATError

/-! Correlated rare products for the complete VHEAT remainder.
These are measure-theoretic inequalities; no independence of the inverse
remainder and evolved trace is used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Positive natural powers retain the exact prime-seminorm exponent. -/
theorem heat_remainder_prime_nat_power
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : ∀ ω,0 ≤ f ω) (p : ℝ) (j : ℕ) (hj : 0 < j) :
    eLpNorm' (fun ω => f ω^j) p μ=eLpNorm' f (p*(j:ℝ)) μ^j := by
  have hjR : 0 < (j:ℝ) := by exact_mod_cast hj
  simpa only [Real.norm_of_nonneg (hf _),Real.rpow_natCast,ENNReal.rpow_natCast] using
    (eLpNorm'_norm_rpow (μ := μ) f p (j:ℝ) hjR)

/-- Hölder pays a complete correlated rare monomial at its exact conjugate
trace exponent. This includes finiteness through extended seminorms. -/
theorem heat_remainder_rare_power_holder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω,0 ≤ R ω) (hT0 : ∀ ω,0 ≤ T ω)
    (j l : ℕ) (hj : 0 < j) (hj128 : j < 128) (hl : 0 < l)
    (e A : ℝ≥0∞) (hRc : eLpNorm' R 128 μ ≤ e)
    (hTc : eLpNorm' T (128*(l:ℝ)/(128-(j:ℝ))) μ ≤ A) :
    eLpNorm' (fun ω => R ω^j*T ω^l) 1 μ ≤ e^j*A^l := by
  have hjR : 0 < (j:ℝ) := by exact_mod_cast hj
  have hj128R : (j:ℝ) < 128 := by exact_mod_cast hj128
  have hden : 0 < 128-(j:ℝ) := sub_pos.mpr hj128R
  have hp : 1 < 128/(j:ℝ) := (one_lt_div hjR).mpr hj128R
  have hconj : (1:ℝ)⁻¹=(128/(j:ℝ))⁻¹+(128/(128-(j:ℝ)))⁻¹ := by
    field_simp
    ring
  have hh := eLpNorm'_le_eLpNorm'_mul_eLpNorm'
    (f := fun ω => R ω^j) (g := fun ω => T ω^l)
    (p := 128/(j:ℝ)) (q := 128/(128-(j:ℝ))) (r := 1)
    (hR.pow j) (hT.pow l) (fun x y : ℝ => x*y) 1
    (Filter.Eventually.of_forall fun _ => by simp only [nnnorm_mul,one_mul,le_refl])
    (by norm_num) hp (by simpa only [one_div] using hconj)
  have hpj : 128/(j:ℝ)*(j:ℝ)=128 := by field_simp
  have hql : 128/(128-(j:ℝ))*(l:ℝ)=128*(l:ℝ)/(128-(j:ℝ)) := by ring
  have hh' : eLpNorm' (fun ω => R ω^j*T ω^l) 1 μ ≤
      eLpNorm' (fun ω => R ω^j) (128/(j:ℝ)) μ*
        eLpNorm' (fun ω => T ω^l) (128/(128-(j:ℝ))) μ := by
    simpa only [Pi.pow_apply,ENNReal.coe_one,one_mul] using hh
  rw [heat_remainder_prime_nat_power μ R hR0 _ j hj,
    heat_remainder_prime_nat_power μ T hT0 _ l hl,hpj,hql] at hh'
  exact hh'.trans (mul_le_mul' (pow_le_pow_left' hRc j) (pow_le_pow_left' hTc l))

/-- Below degree twenty, both rare orders use only the L20 trace cap. -/
theorem heat_remainder_rare_power_below_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω,0 ≤ R ω) (hT0 : ∀ ω,0 ≤ T ω)
    (j : Fin 2) (l : ℕ) (hl : 0 < l) (hl20 : l < 20)
    (e X : ℝ≥0∞) (hRc : eLpNorm' R 128 μ ≤ e)
    (hTc : eLpNorm' T 20 μ ≤ X) :
    eLpNorm' (fun ω => R ω^(j.val+1)*T ω^l) 1 μ ≤ e^(j.val+1)*X^l := by
  have hlR : 0 < (l:ℝ) := by exact_mod_cast hl
  have hl19 : (l:ℝ) ≤ 19 := by exact_mod_cast (show l ≤ 19 by omega)
  have hq0 : 0 < 128*(l:ℝ)/(128-((j.val+1:ℕ):ℝ)) := by
    fin_cases j <;> norm_num <;> positivity
  have hq20 : 128*(l:ℝ)/(128-((j.val+1:ℕ):ℝ)) ≤ 20 := by
    fin_cases j <;> norm_num <;> linarith only [hl19]
  exact heat_remainder_rare_power_holder μ R T hR hT hR0 hT0 (j.val+1) l
    (by omega) (by omega) hl e X hRc
    ((eLpNorm'_le_eLpNorm'_of_exponent_le hq0 hq20 μ hT).trans hTc)

/-- The top-degree rare monomial has interpolation fraction j/108 before
raising to degree twenty, yielding exactly jp/(128-p) in VHEAT (9). -/
theorem heat_remainder_top_trace_interpolation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → ℝ)
    (hT : AEStronglyMeasurable T μ) (j : Fin 2) (X F : ℝ≥0∞)
    (h20 : eLpNorm' T 20 μ ≤ X) (h128 : eLpNorm' T 128 μ ≤ F) :
    eLpNorm' T (2560/(128-((j.val+1:ℕ):ℝ))) μ ≤
      X^(1-((j.val+1:ℕ):ℝ)/108)*F^(((j.val+1:ℕ):ℝ)/108) := by
  have hqlo : (20:ℝ) ≤ 2560/(128-((j.val+1:ℕ):ℝ)) := by fin_cases j <;> norm_num
  have hqhi : 2560/(128-((j.val+1:ℕ):ℝ)) ≤ (128:ℝ) := by fin_cases j <;> norm_num
  have hh := native_source_eLpNorm_interpolate μ T hT 20 128 _
    (by norm_num) (by norm_num) hqlo hqhi X F h20 h128
  convert hh using 1
  fin_cases j <;> norm_num

/-- Complete top-degree correlated rare product, before real-envelope conversion. -/
theorem heat_remainder_rare_power_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R T : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω,0 ≤ R ω) (hT0 : ∀ ω,0 ≤ T ω)
    (j : Fin 2) (e X F : ℝ≥0∞) (hRc : eLpNorm' R 128 μ ≤ e)
    (h20 : eLpNorm' T 20 μ ≤ X) (h128 : eLpNorm' T 128 μ ≤ F) :
    eLpNorm' (fun ω => R ω^(j.val+1)*T ω^20) 1 μ ≤
      e^(j.val+1)*(X^(1-((j.val+1:ℕ):ℝ)/108)*F^(((j.val+1:ℕ):ℝ)/108))^20 := by
  apply heat_remainder_rare_power_holder μ R T hR hT hR0 hT0 (j.val+1) 20
    (by omega) (by omega) (by norm_num) _ _ hRc
  norm_num only [Nat.cast_ofNat,mul_one]
  exact heat_remainder_top_trace_interpolation μ T hT j X F h20 h128

end
end ASDExplicitGamma.Native
