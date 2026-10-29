module

public import ASDExplicitGamma.Native.GenericSourceHolderProducts
public import ASDExplicitGamma.Native.GenericSourceInverseTrace
public import ASDExplicitGamma.Native.GenericSourcePass

/-! Actual L20 bounds in the literal finite-pass profile notation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

private theorem sourceOfReal_min (a b : ℝ) :
    min (ENNReal.ofReal a) (ENNReal.ofReal b) = ENNReal.ofReal (min a b) := by
  rcases le_total a b with hh | hh
  · rw [min_eq_left hh,min_eq_left (ENNReal.ofReal_le_ofReal hh)]
  · rw [min_eq_right hh,min_eq_right (ENNReal.ofReal_le_ofReal hh)]

/-- Normalize the actual trace Holder minima to their literal real source
expressions, retaining both interpolation powers. -/
theorem native_source_full_trace_holder_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [hprob : IsProbabilityMeasure μ]
    (T F : Ω → ℝ) (hT : AEStronglyMeasurable T μ)
    (hT0 : ∀ᵐ ω ∂μ, 0 ≤ T ω) (hF : F = fun ω => 4+T ω)
    (j : Fin 2) (x f : ℝ) (hx : 0 ≤ x) (hf : 0 ≤ f)
    (h20 : eLpNorm' T 20 μ ≤ ENNReal.ofReal x)
    (h128 : eLpNorm' F 128 μ ≤ ENNReal.ofReal f) :
    eLpNorm' F (nativeSourceHolderOrder j) μ ≤ ENNReal.ofReal
      (min f (4+x^(1-((j.val+1:ℕ):ℝ)*(5/27:ℝ))*f^(((j.val+1:ℕ):ℝ)*(5/27:ℝ)))) := by
  have hh := native_source_full_trace_holder_minimum μ T F hT hT0 hF j
    (ENNReal.ofReal x) (ENNReal.ofReal f) h20 h128
  have hp0 : 0 ≤ 1-((j.val+1:ℕ):ℝ)*(5/27:ℝ) := by fin_cases j <;> norm_num
  have hp1 : 0 ≤ ((j.val+1:ℕ):ℝ)*(5/27:ℝ) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hx hp0,ENNReal.ofReal_rpow_of_nonneg hf hp1,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hx _),
    ← ENNReal.ofReal_add (by norm_num : (0:ℝ)≤4) (by positivity),sourceOfReal_min] at hh
  exact hh

/-- The two actual inverse/full-trace products have exactly the finite-pass
source caps b*u1 and b^2*u2. -/
theorem native_source_refined_product_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [hprob : IsProbabilityMeasure μ]
    (P T F : Ω → ℝ) (hP : AEStronglyMeasurable P μ) (hT : AEStronglyMeasurable T μ)
    (hT0 : ∀ᵐ ω ∂μ, 0 ≤ T ω) (hF : F = fun ω => 4+T ω)
    (x f : ℝ) (hx : 0 ≤ x) (hf : 0 ≤ f)
    (hP128 : eLpNorm' P 128 μ ≤ ENNReal.ofReal nativeSourceB128)
    (hT20 : eLpNorm' T 20 μ ≤ ENNReal.ofReal x)
    (hF128 : eLpNorm' F 128 μ ≤ ENNReal.ofReal f) :
    eLpNorm' (fun ω => P ω*F ω) 20 μ ≤ ENNReal.ofReal
      (nativeSourceB128*nativeSourceInterpolationU1 x f) ∧
    eLpNorm' (fun ω => (P ω)^2*F ω) 20 μ ≤ ENNReal.ofReal
      (nativeSourceB128^2*nativeSourceInterpolationU2 x f) := by
  have hFm : AEStronglyMeasurable F μ := by rw [hF]; exact aestronglyMeasurable_const.add hT
  have hu1 := native_source_full_trace_holder_real μ T F hT hT0 hF 0 x f hx hf hT20 hF128
  have hu2 := native_source_full_trace_holder_real μ T F hT hT0 hF 1 x f hx hf hT20 hF128
  norm_num only [nativeSourceHolderOrder,Fin.val_zero,Nat.zero_add,Nat.cast_one,Fin.val_one,
    Nat.cast_ofNat] at hu1 hu2
  have hu1' : eLpNorm' F (640/27) μ ≤ ENNReal.ofReal (nativeSourceInterpolationU1 x f) := by
    convert hu1 using 1
    norm_num [nativeSourceInterpolationU1,nativeSourceEll]
  have hu2' : eLpNorm' F (320/11) μ ≤ ENNReal.ofReal (nativeSourceInterpolationU2 x f) := by
    convert hu2 using 1
    norm_num [nativeSourceInterpolationU2,nativeSourceEll]
  constructor
  · have hh := native_source_holder_one μ P F hP hFm _ _ hP128 hu1'
    rwa [← ENNReal.ofReal_mul (by norm_num [nativeSourceB128])] at hh
  · have hh := native_source_holder_two μ P F hP hFm _ _ hP128 hu2'
    rw [← ENNReal.ofReal_pow (by norm_num [nativeSourceB128]),
      ← ENNReal.ofReal_mul (sq_nonneg _)] at hh
    exact hh

/-- The duality and bank bounds give the literal d-minimum. -/
theorem native_source_refined_inverse_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [hprob : IsProbabilityMeasure μ]
    (P T D : Ω → ℝ) (hP : AEStronglyMeasurable P μ) (hT : AEStronglyMeasurable T μ)
    (hP0 : ∀ᵐ ω ∂μ, 0 ≤ P ω) (hT0 : ∀ᵐ ω ∂μ, 0 ≤ T ω) (hD0 : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    (hDbank : ∀ᵐ ω ∂μ, D ω ≤ 2*P ω)
    (hDtrace : ∀ᵐ ω ∂μ, D ω ≤ 2+T ω+Real.sqrt (2*T ω))
    (x : ℝ) (hx : 0 ≤ x)
    (hP128 : eLpNorm' P 128 μ ≤ ENNReal.ofReal nativeSourceB128)
    (hT20 : eLpNorm' T 20 μ ≤ ENNReal.ofReal x) :
    eLpNorm' D 20 μ ≤ ENNReal.ofReal (nativeSourceInterpolationD x) := by
  have hp20 := (eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num : (0:ℝ)<20)
    (by norm_num : (20:ℝ)≤128) μ hP).trans hP128
  have hb : eLpNorm' D 20 μ ≤ ENNReal.ofReal (2*nativeSourceB128) := by
    have hh : eLpNorm' D 20 μ ≤ eLpNorm' ((2:ℝ) • P) 20 μ := by
      apply eLpNorm'_mono_ae (by norm_num : (0:ℝ)≤20)
      filter_upwards [hP0,hD0,hDbank] with ω hPω hDω hω
      simpa only [Pi.smul_apply,smul_eq_mul,Real.norm_of_nonneg hDω,
        Real.norm_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hPω)] using hω
    rw [eLpNorm'_const_smul 2 (by norm_num : (0:ℝ)<20),Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤2)] at hh
    apply (hh.trans (mul_le_mul' le_rfl hp20)).trans_eq
    exact (ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)).symm
  have ht := native_source_inverse_trace_L20 μ T D hT hT0 hD0 hDtrace _ hT20
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0:ℝ)≤1/2),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_add (by norm_num : (0:ℝ)≤2) hx,
    ← ENNReal.ofReal_add (by positivity) (by positivity),← Real.sqrt_eq_rpow,
    ← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at ht
  rw [nativeSourceInterpolationD,← sourceOfReal_min]
  exact le_min hb ht

end
end ASDExplicitGamma.Native
