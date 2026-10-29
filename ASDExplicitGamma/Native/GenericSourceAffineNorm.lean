module

public import ASDExplicitGamma.Native.GenericSourceBandFactors

/-! Positive affine comparison of finite source L20 seminorms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A pointwise positive affine frame map transfers an actual prime norm
cap. The comparison preserves the constant frame correction. -/
theorem native_source_affine_L20_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hfm : AEStronglyMeasurable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (R A C x : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C) (hx0 : 0 ≤ x)
    (hx : eLpNorm' f 20 μ ≤ ENNReal.ofReal x)
    (hpoint : ∀ ω, g ω ≤ R*(A*f ω+C)) :
    eLpNorm' g 20 μ ≤ ENNReal.ofReal (R*(A*x+C)) := by
  have hnorm : eLpNorm' g 20 μ ≤ eLpNorm' (fun ω => R*(A*f ω+C)) 20 μ := by
    apply eLpNorm'_mono_ae (by norm_num : (0:ℝ)≤20)
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hg0 ω),Real.norm_of_nonneg
        (mul_nonneg hR (add_nonneg (mul_nonneg hA (hf0 ω)) hC))]
      exact hpoint ω
  have houter : eLpNorm' (fun ω => R*(A*f ω+C)) 20 μ =
      ENNReal.ofReal R*eLpNorm' (fun ω => A*f ω+C) 20 μ := by
    have he := eLpNorm'_const_smul (f := fun ω => A*f ω+C) R (μ := μ) (by norm_num : (0:ℝ)<20)
    have hefun : (R • (fun ω => A*f ω+C))=(fun ω => R*(A*f ω+C)) := by funext ω; rfl
    rw [hefun] at he
    simpa only [Real.enorm_eq_ofReal hR] using he
  have hinner : eLpNorm' (fun ω => A*f ω) 20 μ = ENNReal.ofReal A*eLpNorm' f 20 μ := by
    have he := eLpNorm'_const_smul (f := f) A (μ := μ) (by norm_num : (0:ℝ)<20)
    have hefun : A • f=(fun ω => A*f ω) := by funext ω; rfl
    rw [hefun] at he
    simpa only [Real.enorm_eq_ofReal hA] using he
  have hadd := eLpNorm'_add_le (f := fun ω => A*f ω) (g := fun _ => C)
    (hfm.const_smul A) aestronglyMeasurable_const (by norm_num : (1:ℝ)≤20)
  rw [hinner,eLpNorm'_const_of_isProbabilityMeasure C (by norm_num),Real.enorm_eq_ofReal hC] at hadd
  rw [houter] at hnorm
  calc
    _ ≤ ENNReal.ofReal R*(ENNReal.ofReal A*ENNReal.ofReal x+ENNReal.ofReal C) :=
      hnorm.trans (mul_le_mul' le_rfl (hadd.trans (add_le_add (mul_le_mul' le_rfl hx) le_rfl)))
    _ = _ := by rw [ENNReal.ofReal_mul hR,ENNReal.ofReal_add (mul_nonneg hA hx0) hC,
      ENNReal.ofReal_mul hA]

end
end ASDExplicitGamma.Native
