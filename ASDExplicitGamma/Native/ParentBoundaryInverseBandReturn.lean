module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBandDrift
public import ASDExplicitGamma.Native.ParentBoundaryInverseFlow
public import ASDExplicitGamma.Native.ParentBoundaryBandEnergy

/-! The actual signed inverse-deficit integral on the simultaneous band.
All physical generator and probability-law inputs are proved internally. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse Set
noncomputable section

/-- The exact actual inverse heat derivative is the integral of its
literal, independently integrable physical generator. -/
theorem parent_boundary_inverse_band_generator_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) :
    ContinuousOn (parentBoundaryBandInverseMean M n height) (Ici 0) ∧
      ∀ t∈Ioi (0:ℝ), HasDerivAt (parentBoundaryBandInverseMean M n height)
        (∫ omega,parentBoundaryBandInverseGenerator M h n height t omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  have hh := parent_boundary_inverse_band_heat M h hM n height hheight
  refine ⟨hh.1,?_⟩
  intro t ht
  have hd := hh.2 t ht
  have he : (1/2:ℝ)*(∫ omega : Cutoff.CutoffSample 2, ∑ i : Fin height,
      modelCovarianceTrace (mainInverseObservable n M.nu (Annealed.sigmaBar M n))
        (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceBandScalar n height t omega)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      ∫ omega,parentBoundaryBandInverseGenerator M h n height t omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with omega
    rw [Finset.mul_sum]
    rfl
  rw [he] at hd
  exact hd

end
end ASDExplicitGamma.Native
