module

public import ASDExplicitGamma.Native.GenericSourceChildBandCoefficient
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport
public import ASDExplicitGamma.Main.FrameEndpoint
public import ASDExplicitGamma.Native.GenericSourceFullResponse

/-! Exact starting and completed endpoints of the refined child-cube path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- The compact completed old scalar gives the actual cutoff trace on any
observation cube and in any fixed frame. -/
theorem native_source_observed_older_trace (M : ABKModel 2) (q m : ℤ) (σ : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable q M.nu σ
      (olderField (closure (cubeSet (originCube 2 q))) m ω) =
      traceDefect (cubeSet (originCube 2 q))
        (Cutoff.coefficientCutoff M.nu m ω).toFun σ := by
  let K := closure (cubeSet (originCube 2 q))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have he : Model.partialInsertedCoefficient M m 0 ω = Cutoff.coefficientCutoff M.nu m ω := by
    ext x i j
    simp [Model.partialInsertedCoefficient,RegCoeffField.add_apply,RegCoeffField.smul_apply]
  have hh := modelTraceObservable_inserted_eq_traceDefect q M ell m hK σ 0 ω
  rw [(native_source_inserted_endpoints K ell m hK ω).1,he] at hh
  exact hh

/-- The refined path starts at the literal completed lag-one trace, rather
than the ordinary mean at observation scale `n`. -/
theorem native_source_child_band_trace_zero (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
      (nativeSourceChildBandScalar n height 0 ω) = cutoffTraceDefect M n (n-1) ω := by
  simp only [nativeSourceChildBandScalar,Real.sqrt_zero,zero_smul,add_zero]
  exact native_source_observed_older_trace M (n-1) n _ ω

/-- The complete fresh band is exactly the actual terminal cutoff, even
though its observation cube is still the child of the old cutoff scale. -/
theorem native_source_child_band_trace_one (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
      (nativeSourceChildBandScalar n height 1 ω) =
      traceDefect (cubeSet (originCube 2 (n-1)))
        (Cutoff.coefficientCutoff M.nu (n+(height:ℤ)) ω).toFun (Annealed.sigmaBar M n) := by
  have hae : responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 (n-1)))) ℝ ℝ
        (nativeSourceChildBandScalar n height 1 ω)) =ᵐ[volume.restrict (cubeSet (originCube 2 (n-1)))]
      (Cutoff.coefficientCutoff M.nu (n+(height:ℤ)) ω).toFun := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_cubeSet (originCube 2 (n-1)))] with x hx
    have hh := native_source_child_band_coefficient_on_cube M n height 1 ω x hx
    simpa only [Real.sqrt_one,full_response_coefficient_unit M n (n+(height:ℤ)) (by omega) ω] using hh
  unfold modelTraceObservable traceDefect
  rw [coarseBlockMatrix_congr_of_ae_eq hae]

/-- The actual initial refined mean is precisely the completed q1 mean. -/
theorem native_source_child_band_mean_zero (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    nativeSourceChildBandMean M n height 0 =
      ∫ ω, cutoffTraceDefect M n (n-1) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
  integral_congr_ae (Filter.Eventually.of_forall (native_source_child_band_trace_zero M n height))

/-- The refined endpoint mean is the literal terminal coefficient-law mean
on the child cube, still expressed in the old completed true frame. -/
theorem native_source_child_band_mean_one (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    nativeSourceChildBandMean M n height 1 =
      ∫ a : RegCoeffField 2, traceDefect (cubeSet (originCube 2 (n-1))) a.toFun
        (Annealed.sigmaBar M n) ∂(Cutoff.coefficientCutoffLaw M (n+(height:ℤ))) := by
  rw [ASDExplicitGamma.Main.main_completed_trace_integral_eq]
  exact integral_congr_ae (Filter.Eventually.of_forall (native_source_child_band_trace_one M n height))
/-- Structural continuity restores the completed true frame after all fresh
shells have been inserted; the mean uses the completed-law frame map. -/
theorem native_source_child_band_completed_mean_frame
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (hg : M.gamma ≤ gammaZero) (hh : height ≤ 1332) :
    (∫ ω, cutoffTraceDefect M (n+(height:ℤ)) (n-1) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      nativeSourceE M.gamma height*nativeSourceChildBandMean M n height 1 := by
  have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M n height
  have hE := native_source_E_ge_three_power M.gamma height M.shellPrefix.gamma_pos.le hg (by omega)
  have hR : (Annealed.sigmaBar M (n+(height:ℤ)):ℝ)/(Annealed.sigmaBar M n:ℝ) ≤
      nativeSourceE M.gamma height :=
    hratio.2.trans (by
      convert hE using 1
      congr 1
      ring)
  rw [native_source_child_band_mean_one]
  change (∫ ω, traceDefect (cubeSet (originCube 2 (n-1)))
    (Cutoff.coefficientCutoff M.nu (n+(height:ℤ)) ω).toFun
      (Annealed.sigmaBar M (n+(height:ℤ)):ℝ) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ _
  rw [←ASDExplicitGamma.Main.main_completed_trace_integral_eq]
  exact ASDExplicitGamma.Main.main_completed_frame_return_of_ratio M (n+(height:ℤ)) (n-1)
    (Annealed.sigmaBar M n) (nativeSourceE M.gamma height)
    (Annealed.sigmaBar_characterization M n).1 hratio.1 hR


end
end ASDExplicitGamma.Native
