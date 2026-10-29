module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBandReturn

/-! A simpler linear envelope for the actual signed inverse cost.
The global-bank improvement pays this envelope in every parent setup. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse Set
noncomputable section

/-- The actual signed inverse cost also obeys the global linear forcing
envelope. All physical lower-generator inputs are discharged. -/
theorem parent_boundary_actual_inverse_linear_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height)
    (hpast : ∀ j<n,nativeInductionState M h j) :
    let Y := parentBoundaryBandDirichletEnergy M h n height
    let kappa := mainKappa (parentBoundaryBandInverseClock M h n height)
    (∫ t in (0:ℝ)..1,-Y*(parentBoundaryBandInverseMean M n height t-2))≤
      Y*(2+mainRho)*kappa/2 := by
  intro Y kappa
  let f := parentBoundaryBandInverseMean M n height
  let df := fun t => ∫ omega,parentBoundaryBandInverseGenerator M h n height t omega
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have hh := parent_boundary_inverse_band_generator_heat M h hM n height hheight
  have hf : ContinuousOn f (Icc (0:ℝ) 1) := hh.1.mono (fun _ ht => ht.1)
  have hdf : ∀ t∈Ioo (0:ℝ) 1,HasDerivAt f (df t) t := fun t ht => hh.2 t ht.1
  have hstart : 2≤f 0 := parent_boundary_inverse_band_initial M n height
  have hdrift : ∀ t∈Ioo (0:ℝ) 1,-kappa*f t-kappa*mainRho≤df t :=
    fun t ht => parent_boundary_inverse_band_drift M h hM hg n height hheight hpast t ht.2.le
  have hY : 0≤Y := (parent_boundary_band_energy_bounds M h n height).1
  have hrho : 0≤2+mainRho := by unfold mainRho mainBeta mainEpsNew; positivity
  have hi : IntervalIntegrable (fun t => -Y*(f t-2)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
    intro t ht
    exact continuousWithinAt_const.mul ((hf t ht).sub continuousWithinAt_const)
  have hj : IntervalIntegrable (fun t : ℝ => Y*(2+mainRho)*(kappa*t)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (continuous_const.mul continuous_id)
  have hbound := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1) hi hj (fun t ht => by
    have hs := parent_boundary_inverse_interior_charge f df Y kappa mainRho hY hf hdf hstart hdrift t ht
    have hexp : 1-Real.exp (-kappa*t)≤kappa*t := by
      have he := Real.add_one_le_exp (-kappa*t)
      linarith only [he]
    exact hs.trans (mul_le_mul_of_nonneg_left hexp (mul_nonneg hY hrho)))
  apply hbound.trans_eq
  have he : (fun t : ℝ => Y*(2+mainRho)*(kappa*t))=(fun t => (Y*(2+mainRho)*kappa)*t) := by
    funext t
    ring
  rw [he,intervalIntegral.integral_const_mul,integral_id]
  norm_num
  ring

end
end ASDExplicitGamma.Native
