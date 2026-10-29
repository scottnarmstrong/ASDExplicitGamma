module

public import ASDExplicitGamma.Gaussian.BandHeat
public import ASDExplicitGamma.Native.GenericSourceActualProfile

/-! The simultaneous finite-band heat path for the generic source mean.
Its old field, whole fresh band and fixed true frame are literal model data. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- Consecutive fresh shell labels above the completed source base. -/
def nativeSourceBandIndex (n : ℤ) (height : ℕ) (i : Fin height) : ℤ := n+(i.val:ℤ)+1

/-- The literal completed old scalar field with a simultaneously inserted
fresh finite band; no spatial-center independence is substituted. -/
def nativeSourceBandScalar (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : C(closure (cubeSet (originCube 2 n)),ℝ) :=
  olderField (closure (cubeSet (originCube 2 n))) n ω+
    Real.sqrt t • modelBand (closure (cubeSet (originCube 2 n)))
      (nativeSourceBandIndex n height) ω

/-- Actual trace mean along the simultaneous source band in the fixed
true frame at its completed starting label. -/
def nativeSourceBandMean (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) : ℝ :=
  ∫ ω : Cutoff.CutoffSample 2, modelTraceObservable n M.nu (Annealed.sigmaBar M n)
    (nativeSourceBandScalar n height t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- Exact actual-model heat identity for the simultaneous source band.
The entire physical band is one Hilbert-series realization; the standing
Gaussian assumption supplies its law internally. -/
theorem native_source_band_mean_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) :
    ∃ (T : BandHilbert height →L[ℝ] C(closure (cubeSet (originCube 2 n)),ℝ))
      (v : ℕ → BandHilbert height) (hA : Summable (fun j => ‖v j‖^2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (modelBand (closure (cubeSet (originCube 2 n))) (nativeSourceBandIndex n height)) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) ∧
      ContinuousOn (nativeSourceBandMean M n height) (Set.Ici 0) ∧
      ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt (nativeSourceBandMean M n height)
        ((1/2:ℝ)*∫ ω : Cutoff.CutoffSample 2,
          modelCovarianceTrace (modelTraceObservable n M.nu (Annealed.sigmaBar M n))
            (fun j => T (v j)) (nativeSourceBandScalar n height t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  let sourceBandHeightNonzero : NeZero height := ⟨by omega⟩
  let K := closure (cubeSet (originCube 2 n))
  let k := nativeSourceBandIndex n height
  have hk : Function.Injective k := by
    intro i j hij
    apply Fin.ext
    dsimp [k,nativeSourceBandIndex] at hij
    omega
  have hk0 (i : Fin height) : n < k i := by dsimp [k,nativeSourceBandIndex]; omega
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  obtain ⟨T,v,hA,hlaw⟩ := exists_modelBand_realization K M h hM k hk
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hh := c1On_bandModelAverage K M ell n hK k hk0 hA T hlaw
    (ContinuousLinearMap.id ℝ C(K,ℝ)) (ContinuousLinearMap.id ℝ C(K,ℝ))
    (modelTraceObservable n M.nu (Annealed.sigmaBar M n)) hΦ
  have hmean : bandModelAverage K M n k
      (ContinuousLinearMap.id ℝ C(K,ℝ)) (ContinuousLinearMap.id ℝ C(K,ℝ))
      (modelTraceObservable n M.nu (Annealed.sigmaBar M n)) =
      nativeSourceBandMean M n height := rfl
  rw [hmean] at hh
  refine ⟨T,v,hA,hlaw,?_,?_⟩
  · simpa only [nativeSourceBandMean,nativeSourceBandScalar,bandModelAverage,
      ContinuousLinearMap.id_apply,k,K] using hh.1
  · intro t ht
    simpa only [nativeSourceBandMean,nativeSourceBandScalar,bandModelAverage,
      ContinuousLinearMap.id_apply,k,K] using hh.2.2.1 t ht

end
end ASDExplicitGamma.Native
