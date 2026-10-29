module

public import ASDExplicitGamma.Native.GenericSourceChildBandIntegral

/-! Quantitative actual p20 derivative along the simultaneous source band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- Actual simultaneous twentieth moment in the completed starting frame. -/
def nativeSourceChildBandMoment (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) : ℝ :=
  nativeSourceChildBandAverage M n height
    (fun x => modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) x^(20:ℝ)) t

theorem native_source_child_band_moment_nonneg (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) :
    0 ≤ nativeSourceChildBandMoment M n height t := by
  apply integral_nonneg
  intro ω
  exact Real.rpow_nonneg (modelTraceObservable_nonneg (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _) _

/-- Exact finite-shell heat derivative for the actual simultaneous moment. -/
theorem native_source_child_band_moment_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) :
    ContinuousOn (nativeSourceChildBandMoment M n height) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (nativeSourceChildBandMoment M n height)
      (∫ ω, nativeSourceChildBandPowerGenerator M h n height t ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t :=
  native_source_child_band_p20_shell_heat M h hM n height hheight

end
end ASDExplicitGamma.Native
