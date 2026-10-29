module

public import ASDExplicitGamma.Native.HeatFiniteRankLimit
public import ASDExplicitGamma.Native.GenericSourceChildBandHeat
public import ASDExplicitGamma.Native.GenericSourceChildBandEndpoint
public import ASDExplicitGamma.Gaussian.PolynomialTests

/-! The actual child moment curve in its OLD true frame, bound to the
finite-band model average and its fixed-operator Gaussian-rank limit. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Filter MeasureTheory Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
open scoped Topology

/-- The actual lag-one child moment curve. Its test uses the OLD frame
`sigmaBar M n` and the fixed molecular parameter `M.nu`; the fresh input is
the complete finite band above `n`. -/
noncomputable def nativeHeatTrueFrameChildTest
    (M : ABKModel 2) (n : ℤ) (k : ℕ) :
    C(closure (cubeSet (originCube 2 (n - 1))), ℝ) → ℝ :=
  fun x => modelTraceObservable (n - 1) M.nu (Annealed.sigmaBar M n) x ^ k

/-- The actual source child moment, as the literal finite-band model carrier. -/
noncomputable def nativeHeatTrueFrameChildMoment
    (M : ABKModel 2) (n : ℤ) (height k : ℕ) (t : ℝ) : ℝ :=
  bandModelAverage
    (closure (cubeSet (originCube 2 (n - 1)))) M n
    (nativeSourceBandIndex n height)
    (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _)
    (nativeHeatTrueFrameChildTest M n k) t

/-- The moment curve is exactly the source's simultaneous finite-band
expectation on the child cube, with the same completed cutoff and true frame. -/
theorem nativeHeatTrueFrameChildMoment_eq_sourceAverage
    (M : ABKModel 2) (n : ℤ) (height k : ℕ) (t : ℝ) :
    nativeHeatTrueFrameChildMoment M n height k t =
      nativeSourceChildBandAverage M n height
        (fun x => modelTraceObservable (n - 1) M.nu (Annealed.sigmaBar M n)
          x ^ k) t := by
  rfl

/-- At zero heat time the actual finite-band carrier is the literal
old-cutoff child trace moment.  This exposes the precise source law that a
cooperative NATIVE_START comparison must bound. -/
theorem nativeHeatTrueFrameChildMoment_zero_eq_oldCutoffMoment
    (M : ABKModel 2) (n : ℤ) (height k : ℕ) :
    nativeHeatTrueFrameChildMoment M n height k 0 =
      ∫ ω : Cutoff.CutoffSample 2,
        cutoffTraceDefect M n (n - 1) ω ^ k
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  rw [nativeHeatTrueFrameChildMoment_eq_sourceAverage]
  unfold nativeSourceChildBandAverage
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [native_source_child_band_trace_zero M n height ω]

/-- The actual source child moment has a finite-rank Gaussian realization,
the fixed-operator series heat identity, and the corresponding fixed-`nu`
pathwise true-frame comparison. No uniform limit as `nu` tends to zero is
asserted. -/
theorem exists_nativeHeatTrueFrameChildMoment_finiteRankLimit
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height k : ℕ) (hheight : 1 ≤ height)
    (t : ℝ) :
    ∃ (T : Gaussian.BandHilbert height →L[ℝ]
        C(closure (cubeSet (originCube 2 (n - 1))), ℝ))
      (v : ℕ → Gaussian.BandHilbert height)
      (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map
          (Gaussian.modelBand
            (closure (cubeSet (originCube 2 (n - 1))))
            (nativeSourceBandIndex n height)) =
        Gaussian.standardGaussianInfinitePi.map
          (Gaussian.gaussianSeriesLimitE hA T) ∧
      Tendsto
        (fun r => nativeHeatFastRandomBaseAverage hA
          ((ContinuousLinearMap.id ℝ
            C(closure (cubeSet (originCube 2 (n - 1))), ℝ)).comp T)
          (nativeHeatTrueFrameChildTest M n k)
          (((Cutoff.cutoffSampleLaw M).toMeasure.map
            (Gaussian.olderField
              (closure (cubeSet (originCube 2 (n - 1)))) n)).map
                (ContinuousLinearMap.id ℝ _)) r t)
        atTop (𝓝 (nativeHeatTrueFrameChildMoment M n height k t)) ∧
      (∀ x s, 0 < s →
        HasDerivAt
            (Gaussian.gaussianSeriesHeatAverage hA T
              (nativeHeatTrueFrameChildTest M n k) x)
            ((1 / 2 : ℝ) *
              Gaussian.gaussianSeriesHeatTraceAverage hA T
                (nativeHeatTrueFrameChildTest M n k) x s) s ∧
          Tendsto
            (fun r => Gaussian.gaussianFastHeatAverage hA T
              (nativeHeatTrueFrameChildTest M n k) x r s)
            atTop (𝓝 (Gaussian.gaussianSeriesHeatAverage hA T
              (nativeHeatTrueFrameChildTest M n k) x s)) ∧
          Tendsto
            (fun r => Gaussian.gaussianFastHeatTraceAverage hA T
              (nativeHeatTrueFrameChildTest M n k) x r s)
            atTop (𝓝 (Gaussian.gaussianSeriesHeatTraceAverage hA T
              (nativeHeatTrueFrameChildTest M n k) x s)) ) ∧
      (∀ s, 0 < s → HasDerivAt
        (nativeHeatTrueFrameChildMoment M n height k)
        ((1 / 2 : ℝ) * bandModelAverage
          (closure (cubeSet (originCube 2 (n - 1)))) M n
          (nativeSourceBandIndex n height)
          (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _)
          (modelCovarianceTrace (nativeHeatTrueFrameChildTest M n k)
            (fun j => T (v j))) s) s) := by
  classical
  let K := closure (cubeSet (originCube 2 (n - 1)))
  let bands := nativeSourceBandIndex n height
  let Φ := nativeHeatTrueFrameChildTest M n k
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp
      (isBounded_cubeSet (originCube 2 (n - 1))).isCompact_closure
  letI : NeZero height := ⟨by omega⟩
  have htrace := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives
    (n - 1) M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    c2_polynomial_pow htrace k
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 (n - 1))).isCompact_closure
  have hbands : ∀ i, n < bands i := by
    intro i
    dsimp [bands, nativeSourceBandIndex]
    omega
  have hbandInj : Function.Injective bands := by
    intro i j hij
    apply Fin.ext
    dsimp [bands, nativeSourceBandIndex] at hij
    omega
  obtain ⟨T, v, hA, hlaw, hconv, hpoint, _, _, hderiv, _, _⟩ :=
    exists_nativeHeat_bandFastAverage_tendsto_trueFrame
      (b := height) K M h hM ell n hK bands hbands hbandInj
      (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _) Φ hΦ t
      n n n le_rfl 1 (by norm_num)
  have hderiv' : ∀ s, 0 < s →
      HasDerivAt (nativeHeatTrueFrameChildMoment M n height k)
        ((1 / 2 : ℝ) * bandModelAverage K M n bands
          (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _)
          (modelCovarianceTrace Φ (fun j => T (v j))) s) s := by
    intro s hs
    change HasDerivAt (bandModelAverage K M n bands
      (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _) Φ)
      ((1 / 2 : ℝ) * bandModelAverage K M n bands
        (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _)
        (modelCovarianceTrace Φ (fun j => T (v j))) s) s
    exact hderiv s hs
  refine ⟨T, v, hA, ?_, ?_, hpoint, hderiv'⟩
  · simpa [bands, K] using hlaw
  · change Tendsto _ atTop (𝓝 (nativeHeatTrueFrameChildMoment M n height k t))
    exact hconv

end ASDExplicitGamma.Native
