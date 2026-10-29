module

public import ASDExplicitGamma.Native.GenericSourceBandGenerator
public import ASDExplicitGamma.Main.InverseDeficitInitial

/-! Actual simultaneous-band inverse observable heat identity and
its genuine completed-law initial value in the fixed starting frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- Actual fixed-frame inverse-trace mean on the simultaneous source band. -/
def parentBoundaryBandInverseMean (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) : ℝ :=
  nativeSourceBandAverage M n height (mainInverseObservable n M.nu (Annealed.sigmaBar M n)) t

/-- The complete simultaneous-band inverse mean has the exact Gaussian
heat derivative, retaining every canonical physical shell covariance. -/
theorem parent_boundary_inverse_band_heat (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (n : ℤ) (height : ℕ) (hheight : 1≤height) :
    ContinuousOn (parentBoundaryBandInverseMean M n height) (Set.Ici 0) ∧
    ∀ t ∈ Set.Ioi (0:ℝ),HasDerivAt (parentBoundaryBandInverseMean M n height)
      ((1/2:ℝ)*∫ omega : Cutoff.CutoffSample 2,∑ i : Fin height,
        modelCovarianceTrace (mainInverseObservable n M.nu (Annealed.sigmaBar M n))
          (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
            (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceBandScalar n height t omega)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t :=
  native_source_band_average_shell_heat M h hM n height hheight _
    (mainInverseObservable_hasPolynomiallyBoundedC2Derivatives n M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1)

/-- The actual band starts at the completed OLD inverse mean. -/
theorem parent_boundary_inverse_band_zero (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    parentBoundaryBandInverseMean M n height 0=mainInverseHeatAverage n M n 0 := by
  rw [congrFun (mainInverseHeatAverage_eq n M n) 0]
  simp only [parentBoundaryBandInverseMean,nativeSourceBandAverage,nativeSourceBandScalar,
    modelHeatAverage,modelInsertedScalar,Real.sqrt_zero,zero_smul,add_zero]

/-- The genuine completed OLD law starts above two; no intermediate
true-frame inverse positivity assertion is introduced. -/
theorem parent_boundary_inverse_band_initial (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    2≤parentBoundaryBandInverseMean M n height 0 := by
  rw [parent_boundary_inverse_band_zero]
  exact main_inverse_heat_initial_ge_two M n n

end
end ASDExplicitGamma.Native
