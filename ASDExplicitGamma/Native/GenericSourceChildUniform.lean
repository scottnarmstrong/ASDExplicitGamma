module

public import ASDExplicitGamma.Native.GenericSourceChildAuxCost
public import ASDExplicitGamma.Native.GenericSourceChildInitial
public import ASDExplicitGamma.Native.GenericSourceChildBandBarrier

/-! Actual uniform child trace caps with the initial moment, physical
variance, full128 bank and strict invariant-region budget all discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse
noncomputable section

/-- The actual refined-child heat path stays under its auxiliary norm
barrier throughout either finite range. Only the causal native past and
the completed starting state enter; no norm bootstrap premise remains. -/
theorem native_source_child_band_uniform_L20_aux
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (high : Bool) (hh : height ≤ nativeSourceChildAuxHeight high) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, eLpNorm'
      (fun ω : Cutoff.CutoffSample 2 => modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (nativeSourceChildBandScalar n height t ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*(nativeSourceChildAuxNorm high:ℝ)) := by
  have ht : 0 < theta M := div_pos M.shellPrefix.gamma_pos (by norm_num [gammaZero])
  rcases native_source_child_aux_certificate high with ⟨_,_,_,hc,_,_,_,_,_,hmargin⟩
  have hcR : (0:ℝ) ≤ nativeSourceChildAuxCost high := by exact_mod_cast hc
  have hmarginR : (250:ℝ)+(nativeSourceChildAuxCost high:ℝ)<(nativeSourceChildAuxNorm high:ℝ) := by
    exact_mod_cast hmargin
  apply native_source_child_band_uniform_cap_of_budget M h hM hg n height hheight hpast hstate
    (250*theta M) (theta M*(nativeSourceChildAuxCost high:ℝ))
    (theta M*(nativeSourceChildAuxNorm high:ℝ))
    (mul_nonneg (by norm_num) ht.le) (mul_nonneg ht.le hcR)
  · have hh := mul_lt_mul_of_pos_left hmarginR ht
    convert hh using 1; ring
  · exact native_source_child_initial_L20 M h hM hg n hpast
  · exact native_source_child_aux_cost M hg height high hh

end
end ASDExplicitGamma.Native
