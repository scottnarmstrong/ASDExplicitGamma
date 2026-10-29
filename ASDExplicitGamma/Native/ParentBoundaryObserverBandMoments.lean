module

public import ASDExplicitGamma.Native.ParentBoundaryObserverBandHeat
public import ASDExplicitGamma.Gaussian.BandModelMoments

/-! Actual Gaussian moments on independent observer squares, with the
completed base and full finite band kept unchanged. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian
open scoped ENNReal
noncomputable section

/-- The actual observer-square scalar field is measurable. -/
theorem parent_boundary_observer_band_scalar_measurable (q n : ℤ) (height : ℕ) (t : ℝ) :
    Measurable (parentBoundaryObserverBandScalar q n height t) := by
  let K := closure (cubeSet (originCube 2 q))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have hs : Measurable (fun omega : Cutoff.CutoffSample 2 => Real.sqrt t •
      modelBand K (nativeSourceBandIndex n height) omega) := by
    change Measurable ((fun _ : Cutoff.CutoffSample 2 => Real.sqrt t) • modelBand K (nativeSourceBandIndex n height))
    exact measurable_const.smul (measurable_modelBand K (nativeSourceBandIndex n height))
  exact (measurable_olderField K ell n hK).add hs

/-- Every measurable polynomial-growth observer test has all finite
Gaussian moments on the literal simultaneous band. -/
theorem parent_boundary_observer_band_test_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (q n : ℤ) (height : ℕ) (hheight : 1≤height)
    (Phi : C(closure (cubeSet (originCube 2 q)),ℝ) → ℝ)
    (hPhi : Measurable Phi) (hgrowth : HasPolynomialGrowth Phi)
    (t p : ℝ) (hp : 2≤p) :
    MemLp (fun omega : Cutoff.CutoffSample 2 => Phi (parentBoundaryObserverBandScalar q n height t omega))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let parentBoundaryObserverMomentHeightNonzero : NeZero height := ⟨by omega⟩
  let K := closure (cubeSet (originCube 2 q))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have hk : Function.Injective (nativeSourceBandIndex n height) := by
    intro i j hij
    apply Fin.ext
    dsimp [nativeSourceBandIndex] at hij
    omega
  obtain ⟨A,v,hA,hlaw⟩ := exists_modelBand_realization K M h hM (nativeSourceBandIndex n height) hk
  exact memLp_bandModel_test K M ell n hK (nativeSourceBandIndex n height) hA A hlaw
    (ContinuousLinearMap.id ℝ C(K,ℝ)) (ContinuousLinearMap.id ℝ C(K,ℝ)) Phi hPhi hgrowth t hp

end
end ASDExplicitGamma.Native
