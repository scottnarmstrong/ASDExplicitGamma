module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBandHeat
public import ASDExplicitGamma.Native.GenericSourceBandFactors
public import ASDExplicitGamma.Main.InverseDeficitBank

/-! The actual simultaneous-band inverse trace and its global-bank cubic
moment. The local root set is unchanged when using the global bank cap. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The two existing inverse tests are literally the same observable. -/
theorem parent_boundary_inverse_observable_eq_bank (n : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma)
    (x : C(closure (cubeSet (originCube 2 n)),ℝ)) :
    mainInverseObservable n nu sigma x=bankInverseTraceObservable n nu sigma hnu hsigma x :=
  mainInverseObservable_eq_twoLoad n nu sigma hnu hsigma x

/-- The same finite population and simultaneous weights satisfy the global
bank, directly from the proved strict-past native states. -/
theorem parent_boundary_inverse_band_global_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t≤1) :
    InverseBankConclusion M .globalInverse (bankLocalRoots (originCube 2 n) 5)
      n (n+(height:ℤ)) (fun _ => Real.sqrt t) := by
  have hgeom := bank_local_roots_geometry (originCube 2 n) 5 (by norm_num)
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hg n hpast).1
  exact global_inverse_bank M h hM hg _ n (n+(height:ℤ)) (by omega) _
    (fun _ _ => ⟨Real.sqrt_nonneg t,Real.sqrt_le_one.mpr ht⟩)
    hgeom.1 hgeom.2 hpast hmean

/-- The actual band inverse observable is nonnegative and bounded by twice
the literal complete local history, without changing its fixed frame. -/
theorem parent_boundary_inverse_band_history_bounds
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t≤1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      0≤mainInverseObservable n M.nu (Annealed.sigmaBar M n)
          (nativeSourceBandScalar n height t omega) ∧
      mainInverseObservable n M.nu (Annealed.sigmaBar M n)
          (nativeSourceBandScalar n height t omega)≤
        2*(nativeSourceBandHistory M n height t omega).toReal := by
  have hs := (Annealed.sigmaBar_characterization M n).1
  filter_upwards [native_source_band_inverse_trace_ae_le M h hM hg n height hpast t ht]
    with omega ho
  rw [parent_boundary_inverse_observable_eq_bank n M.nu _ M.nu_pos hs]
  exact ⟨native_source_model_inverse_trace_nonneg n M.nu _ M.nu_pos hs _,ho⟩

/-- Measurability of the actual fixed-frame inverse trace along the band. -/
theorem parent_boundary_inverse_band_observable_measurable
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) :
    Measurable (fun omega : Cutoff.CutoffSample 2 =>
      mainInverseObservable n M.nu (Annealed.sigmaBar M n)
        (nativeSourceBandScalar n height t omega)) :=
  (mainInverseObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
      (native_source_band_scalar_measurable n height t)

/-- The actual correlated cubic moment keeps the same bank and its complete
reserve. No independence or additional norm premise is used. -/
theorem parent_boundary_inverse_band_cubic_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t≤1) :
    (∫ omega : Cutoff.CutoffSample 2,
      (nativeSourceBandHistory M n height t omega).toReal^2*
        mainInverseObservable n M.nu (Annealed.sigmaBar M n)
          (nativeSourceBandScalar n height t omega) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (inverseBankCap .globalInverse:ℝ)^2*parentBoundaryBandInverseMean M n height t+
        2*(2*(inverseBankCap .globalInverse:ℝ)^2*(inverseBankReserve .globalInverse:ℝ)+
          3*(inverseBankCap .globalInverse:ℝ)*(inverseBankReserve .globalInverse:ℝ)^2+
          (inverseBankReserve .globalInverse:ℝ)^3) :=
  main_inverse_deficit_cubic_integral_bound_of_global_bank M (bankLocalRoots (originCube 2 n) 5)
    n (n+(height:ℤ)) (fun _ => Real.sqrt t) _
    (parent_boundary_inverse_band_global_bank M h hM hg n height hpast t ht)
    (parent_boundary_inverse_band_observable_measurable M n height t)
    (parent_boundary_inverse_band_history_bounds M h hM hg n height hpast t ht)

end
end ASDExplicitGamma.Native
