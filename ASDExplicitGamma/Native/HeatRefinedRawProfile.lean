module

public import ASDExplicitGamma.Native.GenericSourceChildBandResponse
public import ASDExplicitGamma.Native.GenericSourceRawTailProfile
public import ASDExplicitGamma.Numerics.Native.Heat009Initial
public import ASDExplicitGamma.Numerics.Native.Heat011Initial

/-! The actual refined full128 response fits the exact pre-heat raw slots. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian
open Numerics.Native
open scoped ENNReal
noncomputable section

/-- Split the two frame clocks BEFORE replacing exponentials by rational E.
This retains the margin in the certified refined raw coordinate. -/
theorem heat_refined_raw_profile_le (gamma : ℝ) (h : ℕ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ 17/50000) (hh : h ≤ 1331) :
    nativeSourceChildFullResponseCap gamma h ≤
      (nativeHeatRQ:ℝ)*nativeSourceGenericFullResponseCap (17/50000) (h+1) := by
  have hE := native_source_E_ge_three_power gamma (h+3) hg0 hg (by omega)
  have hE1 := native_source_E_ge_three_power gamma 1 hg0 hg (by omega)
  norm_num only [Nat.cast_one] at hE1
  have hE1cap : nativeSourceE gamma 1 ≤ (nativeHeatRQ:ℝ) := by
    have hh := native_source_E_le_endpoint gamma 1 hg0 hg (by norm_num)
    simpa [nativeSourceE,nativeHeatRQ,nativeE,nativeGamma] using hh
  have hcap := native_source_generic_full_response_cap_degree gamma (h+1) hg0 hg (by omega)
  have hcap0 := native_source_generic_full_response_cap_nonneg gamma (h+1) hg0 hg (by omega)
  have hRQ : (0:ℝ) ≤ nativeHeatRQ := by norm_num [nativeHeatRQ,nativeE,nativeGamma]
  have hexp : (2*(h:ℝ)+8)*gamma = 2*((h+3:ℕ):ℝ)*gamma+2*(1:ℝ)*gamma := by push_cast; ring
  have hfirst : nativeSourceChildFullResponseCap gamma h ≤
      nativeSourceE gamma 1*nativeSourceGenericFullResponseCap gamma (h+1) := by
    unfold nativeSourceChildFullResponseCap
    rw [hexp,Real.rpow_add (by norm_num : (0:ℝ)<3)]
    simp only [mul_one]
    calc
      _ ≤ 4*((1009309/500000:ℝ)+gamma*(32474*((h:ℝ)+2)+11483216))*
          (nativeSourceE gamma (h+3)*nativeSourceE gamma 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hE hE1 (by positivity)
          (native_source_E_nonneg gamma (h+3) hg0 hg (by omega))) (by positivity)
      _ = nativeSourceE gamma 1*nativeSourceGenericFullResponseCap gamma (h+1) := by
        unfold nativeSourceGenericFullResponseCap
        push_cast
        ring
  exact hfirst.trans (mul_le_mul hE1cap hcap hcap0 hRQ)

/-- The literal refined physical full trace, along the simultaneous band,
fits the split-clock full128 profile from strict-past states alone. -/
theorem heat_refined_child_physical_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hh : height ≤ 1331)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1) :
    eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (nativeSourceChildBandScalar n height t ω)+4) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((nativeHeatRQ:ℝ)*nativeSourceGenericFullResponseCap (17/50000) (height+1)) :=
  (native_source_child_band_full_response_L128 M h hM hg n height hpast t ht).trans
    (ENNReal.ofReal_le_ofReal (heat_refined_raw_profile_le M.gamma height M.shellPrefix.gamma_pos.le
      (by simpa only [gammaZero] using hg) hh))

end
end ASDExplicitGamma.Native
