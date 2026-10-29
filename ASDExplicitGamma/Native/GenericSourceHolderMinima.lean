module

public import ASDExplicitGamma.Native.GenericSourceInterpolation
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-! The actual trace-norm interpolation consumed by the four generic source
passes. Both Holder orders and both finite minima are retained exactly. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The order paired with one or two order-128 inverse factors at p=20. -/
def nativeSourceHolderOrder (j : Fin 2) : ℝ :=
  2560/(128-20*((j.val+1:ℕ):ℝ))

/-- Both source Holder orders lie strictly between the two supplied orders. -/
theorem native_source_holder_order_bounds (j : Fin 2) :
    20 ≤ nativeSourceHolderOrder j ∧ nativeSourceHolderOrder j ≤ 128 := by
  fin_cases j <;> norm_num [nativeSourceHolderOrder]

/-- The interpolation powers are exactly 1-j ell and j ell, ell=5/27,
for j=1,2; no replacement by an all-order cap occurs. -/
theorem native_source_trace_interpolation_20_128 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℝ) (hT : AEStronglyMeasurable T μ)
    (j : Fin 2) (A B : ℝ≥0∞)
    (h20 : eLpNorm' T 20 μ ≤ A) (h128 : eLpNorm' T 128 μ ≤ B) :
    eLpNorm' T (nativeSourceHolderOrder j) μ ≤
      A^(1-((j.val+1:ℕ):ℝ)*(5/27:ℝ))*B^(((j.val+1:ℕ):ℝ)*(5/27:ℝ)) := by
  have hh := native_source_eLpNorm_interpolate μ T hT 20 128 (nativeSourceHolderOrder j)
    (by norm_num) (by norm_num) (native_source_holder_order_bounds j).1
    (native_source_holder_order_bounds j).2 A B h20 h128
  convert hh using 1
  fin_cases j <;> norm_num [nativeSourceHolderOrder]

/-- Full trace F=4+T obeys both terms of the source finite-Holder minimum.
The defect's high-order cap is supplied by its actual full trace, using T≥0. -/
theorem native_source_full_trace_holder_minimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [hprob : IsProbabilityMeasure μ]
    (T F : Ω → ℝ) (hT : AEStronglyMeasurable T μ)
    (hT0 : ∀ᵐ ω ∂μ, 0 ≤ T ω) (hF : F = fun ω => 4+T ω)
    (j : Fin 2) (A B : ℝ≥0∞)
    (h20 : eLpNorm' T 20 μ ≤ A) (h128 : eLpNorm' F 128 μ ≤ B) :
    eLpNorm' F (nativeSourceHolderOrder j) μ ≤
      min B (ENNReal.ofReal 4+
        A^(1-((j.val+1:ℕ):ℝ)*(5/27:ℝ))*B^(((j.val+1:ℕ):ℝ)*(5/27:ℝ))) := by
  have hq : 0 < nativeSourceHolderOrder j := (by norm_num : (0:ℝ)<20).trans_le
    (native_source_holder_order_bounds j).1
  have hFmeas : AEStronglyMeasurable F μ := by rw [hF]; exact aestronglyMeasurable_const.add hT
  have hT128 : eLpNorm' T 128 μ ≤ B := by
    apply (eLpNorm'_mono_ae (by norm_num : (0:ℝ)≤128) _).trans h128
    filter_upwards [hT0] with ω hω
    rw [hF,Real.norm_of_nonneg hω,Real.norm_of_nonneg (by positivity : (0:ℝ)≤4+T ω)]
    linarith only [hω]
  have hi := native_source_trace_interpolation_20_128 μ T hT j A B h20 hT128
  apply le_min
  · exact (eLpNorm'_le_eLpNorm'_of_exponent_le hq (native_source_holder_order_bounds j).2 μ hFmeas).trans h128
  · have ht := eLpNorm'_add_le (f := fun _ : Ω => (4:ℝ)) (g := T) aestronglyMeasurable_const hT
      ((by norm_num : (1:ℝ)≤20).trans (native_source_holder_order_bounds j).1)
    rw [eLpNorm'_const_of_isProbabilityMeasure 4 hq,Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤4)] at ht
    rw [hF]
    exact ht.trans (add_le_add le_rfl hi)

end
end ASDExplicitGamma.Native
