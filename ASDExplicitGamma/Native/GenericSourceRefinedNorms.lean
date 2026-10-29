module

public import ASDExplicitGamma.Native.GenericSourceInitialRoot
public import ASDExplicitGamma.Native.GenericSourceFunctionalCaps
public import ASDExplicitGamma.Native.GenericSourceActualInverse

/-! The literal finite-pass norm minima for the actual source law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Convert a finite prime L20 cap to its actual nonnegative real norm. -/
theorem native_source_real_norm_le_of_prime_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω) (A : ℝ) (hA : 0 ≤ A)
    (hcap : eLpNorm' f 20 μ ≤ ENNReal.ofReal A) : positiveLpNorm μ 20 f ≤ A := by
  have he : eLpNorm f (ENNReal.ofReal 20) μ = eLpNorm' f 20 μ := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤20)] using
      eLpNorm_eq_eLpNorm' (by norm_num : ENNReal.ofReal (20:ℝ)≠0)
        ENNReal.ofReal_ne_top hf
  have hc := he.le.trans hcap
  have hmem : MemLp f (ENNReal.ofReal 20) μ := memLp_iff.mpr (hc.trans_lt ENNReal.ofReal_lt_top)
  rw [positiveLpNorm_eq_eLpNorm_toReal μ (by norm_num) f hf0 hmem]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hc).trans_eq (ENNReal.toReal_ofReal hA)

end
end ASDExplicitGamma.Native
