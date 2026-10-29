module

public import ASDExplicitGamma.Native.GenericSourceChildBandHeat
public import ASDExplicitGamma.Inverse.SourceQ3PowerIdentity

/-! Exact p20 heat identity on the simultaneous actual source band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- The actual simultaneous twentieth moment has the complete finite sum
of the canonical shell power generators as its derivative. -/
theorem native_source_child_band_p20_shell_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) :
    let Φ := modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
    ContinuousOn (nativeSourceChildBandAverage M n height (fun x => Φ x^(20:ℝ))) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (nativeSourceChildBandAverage M n height (fun x => Φ x^(20:ℝ)))
      (∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        modelPowerHeatGenerator Φ
          (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) 20 (nativeSourceChildBandScalar n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  let Φ := modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hΦ0 := modelTraceObservable_nonneg (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1
  have hh := native_source_child_band_average_shell_heat M h hM n height hheight (fun x => Φ x^(20:ℝ))
    (hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦ0 (by norm_num : (2:ℝ)≤20))
  refine ⟨hh.1,?_⟩
  intro t ht
  have hd := hh.2 t ht
  have he : (1/2:ℝ)*(∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
      modelCovarianceTrace (fun x => Φ x^(20:ℝ))
        (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceChildBandScalar n height t ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
        modelPowerHeatGenerator Φ
          (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) 20 (nativeSourceChildBandScalar n height t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact source_q3_covariance_power_identity (n-1) M.nu (Annealed.sigmaBar M n)
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (q3ModelLength (n+((i.val+1:ℕ):ℤ))) _
  rw [he] at hd
  exact hd

end
end ASDExplicitGamma.Native
