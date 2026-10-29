module

public import ASDExplicitGamma.Native.GenericSourceBandEndpoint
public import ASDExplicitGamma.Native.GenericSourceAffineNorm
public import ASDExplicitGamma.Inverse.SourceFramePhysical

/-! The literal weak-frame cap on the actual completed source trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- The actual completed defect has the exact L20 frame cap,
including its quadratic correction at the true band gap. -/
theorem native_source_completed_generic_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height) (hh : height ≤ 1332) :
    eLpNorm' (cutoffTraceDefect M (n+(height:ℤ)) n) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeSourceWeakFrame M.gamma height
        (nativeSourceGenericIndividualProfile M.gamma (theta M) height)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := fun ω : Cutoff.CutoffSample 2 => modelTraceObservable n M.nu (Annealed.sigmaBar M n)
    (nativeSourceBandScalar n height 1 ω)
  let g := cutoffTraceDefect M (n+(height:ℤ)) n
  let eta := nativeSourceFrameEta
  let A := 1+eta
  let C := 8*(1+1/eta)*((11/10:ℝ)*M.gamma*(height:ℝ))^2
  let R := nativeSourceE M.gamma height
  let x := nativeSourceGenericIndividualProfile M.gamma (theta M) height
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hx0 : 0 ≤ x := native_source_generic_individual_profile_nonneg M.gamma (theta M) height hg0 ht0 hg hh
  have hR : 0 ≤ R := native_source_E_nonneg M.gamma height hg0 hg (by omega)
  have hA : 0 ≤ A := by norm_num [A,eta,nativeSourceFrameEta]
  have hC : 0 ≤ C := by dsimp [C,eta,nativeSourceFrameEta]; positivity
  have hfm : AEStronglyMeasurable f μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
        (native_source_band_scalar_measurable n height 1)).aestronglyMeasurable
  have hf0 (ω) : 0 ≤ f ω := modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _
  have hg_nonneg (ω) : 0 ≤ g ω := cutoffTraceDefect_nonneg M (n+(height:ℤ)) n ω
  have hcap : eLpNorm' f 20 μ ≤ ENNReal.ofReal x :=
    native_source_band_generic_individual_profile M h hM hg n hpast hstate height hheight hh 1 (by constructor <;> norm_num)
  have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M n height
  have hE := native_source_E_ge_three_power M.gamma height hg0 hg (by omega)
  have hratioR : (Annealed.sigmaBar M (n+(height:ℤ)):ℝ)/(Annealed.sigmaBar M n:ℝ) ≤ R :=
    hratio.2.trans (by convert hE using 1; congr 1; ring)
  have hpoint (ω) : g ω ≤ R*(A*f ω+C) := by
    have hmap := source_cutoff_pathwise_frame_map M n (n+(height:ℤ)) n ω (by omega)
      eta (by norm_num [eta,nativeSourceFrameEta])
    have hgap : ((n+(height:ℤ):ℤ):ℝ)-(n:ℝ)=(height:ℝ) := by push_cast; ring
    rw [hgap,←native_source_band_trace_one M n height ω] at hmap
    exact hmap.trans (mul_le_mul_of_nonneg_right hratioR (add_nonneg (mul_nonneg hA (hf0 ω)) hC))
  exact native_source_affine_L20_cap μ f g hfm hf0 hg_nonneg R A C x hR hA hC hx0 hcap hpoint

end
end ASDExplicitGamma.Native
