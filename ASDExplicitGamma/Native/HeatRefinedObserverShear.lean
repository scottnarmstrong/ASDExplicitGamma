module

public import ASDExplicitGamma.Native.HeatRefinedObserverInverse
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandTrace
public import ASDExplicitGamma.Native.ParentBoundaryShearTrace

/-! Actual auxiliary gauges on the refined observer in the starting parent frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic
open Algsuperdiff.Section3
noncomputable section

/-- The auxiliary constant changes the test on the observer, not the physical
coefficient across the parent. -/
def heatRefinedObserverShear (q n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (g : ℝ) : C(closure (cubeSet (originCube 2 q)),ℝ) :=
  parentBoundaryObserverBandScalar q n height t ω+ContinuousMap.const _ g

/-- Sharp pointwise auxiliary trace envelope at the REFINED observer.
The physical trace and inverse reserve remain on the same sample. -/
theorem heat_refined_observer_shear_trace_ae_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (q n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (hq : originCube 2 q ∈ descendantsAtDepth (originCube 2 n) r)
    (height : ℕ) (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,∀ g : ℝ,
      modelTraceObservable q M.nu (Annealed.sigmaBar M n) (heatRefinedObserverShear q n height t ω g) ≤
      (Real.sqrt (modelTraceObservable q M.nu (Annealed.sigmaBar M n)
          (parentBoundaryObserverBandScalar q n height t ω))+
        |g/(Annealed.sigmaBar M n:ℝ)| *
          Real.sqrt (2*((3683/2500:ℝ)+nativeSourceBandRemainder M n height t ω)))^2 := by
  filter_upwards [heat_refined_observer_inverse_ae_le M h hM hg q n r hr hq height hpast t ht] with ω hω
  intro g
  have hsum := add_le_add (le_refl (Real.sqrt (modelTraceObservable q M.nu
    (Annealed.sigmaBar M n) (parentBoundaryObserverBandScalar q n height t ω))))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hω)
      (abs_nonneg (g/(Annealed.sigmaBar M n:ℝ))))
  exact (parent_boundary_model_trace_shear_upper q M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (parentBoundaryObserverBandScalar q n height t ω) g).trans
      (pow_le_pow_left₀ (by positivity) hsum 2)

end
end ASDExplicitGamma.Native
