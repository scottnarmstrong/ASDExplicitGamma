module

public import ASDExplicitGamma.Native.HeatCooperativeFiniteRankLimit
public import ASDExplicitGamma.Native.HeatVHEATError
public import ASDExplicitGamma.Native.RefinedHeatConclusion

/-! A source-parameter specialization of the full cooperative heat curve. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Filter MeasureTheory Set Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped Topology

/-- The actual cooperative moment in the OLD true frame: it uses the source
diffusivity and the completed source label's annealed frame. -/
noncomputable def nativeHeatTrueFrameCooperativeMoment
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (m : ℤ) (bands : Fin b → ℤ)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ))
    (k : ℕ) (θ t : ℝ) : ℝ :=
  nativeHeatChildBandMoment U hU hvol M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 K M m bands P L
    hA T k θ t

/-- The exact canceled generator of the actual cooperative moment curve in
the OLD true frame. The direction sequence is that of its finite-band
Gaussian realization. -/
noncomputable def nativeHeatTrueFrameCooperativeGenerator
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (m : ℤ) (bands : Fin b → ℤ)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ))
    (k : ℕ) (θ t : ℝ) : ℝ :=
  nativeHeatChildBandMomentGenerator U hU hvol M.nu
    (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 K M m bands P L
    (v := v) hA T k θ t

/-- At the backward-heat starting time the actual cooperative moment is the
source band's true-frame average with auxiliary variance `1 + θ`. -/
theorem nativeHeatTrueFrameCooperativeMoment_start_eq_actualBandAverage
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (m : ℤ) (bands : Fin b → ℤ)
    (hbands : ∀ i, m < bands i)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ)) {θ : ℝ} (hθ : 0 < θ)
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K bands) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)) (k : ℕ) :
    nativeHeatTrueFrameCooperativeMoment U hU hvol K M m bands P L hA T
        k θ 0 =
      bandModelAverage K M m bands P
        ((childConstantMap (fun i => closure (U i))).comp L)
        (childPower U hU hvol M.nu (Annealed.sigmaBar M m)
          M.nu_pos (Annealed.sigmaBar_characterization M m).1 k) (1 + θ) := by
  exact nativeHeatChildBandMoment_start_eq_actualBandAverage
    U hU hvol M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 K M m bands hbands P L hA T
    hθ hlaw k

/-- The full cooperative moment system has one source-law finite-band
realization and its fixed-`M.nu` Gaussian-series limit, in the same OLD true
frame used by the refined-heat contract. The resulting moment curve is the
named `nativeHeatTrueFrameCooperativeMoment`, not an auxiliary surrogate. -/
theorem exists_nativeHeatTrueFrameCooperativeMomentCurve_finiteRankLimit
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell))
    (bands : Fin b → ℤ) (hbands : ∀ i, m < bands i)
    (hbandsInj : Function.Injective bands)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ)) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (T : BandHilbert b →L[ℝ] C(K, ℝ))
      (v : ℕ → BandHilbert b) (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K bands) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) ∧
      (∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
        Tendsto
          (fun r => nativeHeatFastRandomBaseAverage hA (P.comp T)
            (backwardTest hA (((childConstantMap
              (fun i => closure (U i))).comp L).comp T)
                (childPower U hU hvol M.nu (Annealed.sigmaBar M m)
                  M.nu_pos (Annealed.sigmaBar_characterization M m).1 k) θ t)
            (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map P)
            r t) atTop
          (𝓝 (nativeHeatTrueFrameCooperativeMoment U hU hvol K M m bands P
            L hA T k θ t))) ∧
      (∀ k : ℕ, ∀ x s, 0 < s →
        HasDerivAt (gaussianSeriesHeatAverage hA
          (((childConstantMap (fun i => closure (U i))).comp L).comp T)
          (childPower U hU hvol M.nu (Annealed.sigmaBar M m)
            M.nu_pos (Annealed.sigmaBar_characterization M m).1 k) x)
          ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA
            (((childConstantMap (fun i => closure (U i))).comp L).comp T)
            (childPower U hU hvol M.nu (Annealed.sigmaBar M m)
              M.nu_pos (Annealed.sigmaBar_characterization M m).1 k) x s) s ∧
        Tendsto (fun r => gaussianFastHeatAverage hA
          (((childConstantMap (fun i => closure (U i))).comp L).comp T)
          (childPower U hU hvol M.nu (Annealed.sigmaBar M m)
            M.nu_pos (Annealed.sigmaBar_characterization M m).1 k) x r s) atTop
          (𝓝 (gaussianSeriesHeatAverage hA
            (((childConstantMap (fun i => closure (U i))).comp L).comp T)
            (childPower U hU hvol M.nu (Annealed.sigmaBar M m)
              M.nu_pos (Annealed.sigmaBar_characterization M m).1 k) x s)) ∧
        Tendsto (fun r => gaussianFastHeatTraceAverage hA
          (((childConstantMap (fun i => closure (U i))).comp L).comp T)
          (childPower U hU hvol M.nu (Annealed.sigmaBar M m)
            M.nu_pos (Annealed.sigmaBar_characterization M m).1 k) x r s) atTop
          (𝓝 (gaussianSeriesHeatTraceAverage hA
            (((childConstantMap (fun i => closure (U i))).comp L).comp T)
            (childPower U hU hvol M.nu (Annealed.sigmaBar M m)
              M.nu_pos (Annealed.sigmaBar_characterization M m).1 k) x s))) ∧
      (∀ k : ℕ, 1 ≤ k →
        ContinuousOn (nativeHeatTrueFrameCooperativeMoment U hU hvol K M m
          bands P L hA T k θ) (Icc 0 1) ∧
        ContinuousOn (nativeHeatTrueFrameCooperativeGenerator U hU hvol K M m
          bands P L hA T k θ) (Icc 0 1) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1,
          HasDerivAt (nativeHeatTrueFrameCooperativeMoment U hU hvol K M m
            bands P L hA T k θ)
            (nativeHeatTrueFrameCooperativeGenerator U hU hvol K M m bands
              P L hA T k θ t) t)) := by
  obtain ⟨T, v, hA, hlaw, hconv, hseries, hderiv⟩ :=
    exists_nativeHeatChildBandMomentCurve_finiteRankLimit
      U hU hvol M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 K M h hM ell m hK
      bands hbands hbandsInj P L hθ
  refine ⟨T, v, hA, hlaw, ?_, hseries, ?_⟩
  · intro k t ht
    simpa [nativeHeatTrueFrameCooperativeMoment] using hconv k t ht
  · intro k hk
    change
      ContinuousOn (nativeHeatChildBandMoment U hU hvol M.nu
        (Annealed.sigmaBar M m) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 K M m bands P L hA T k θ)
        (Icc 0 1) ∧
      ContinuousOn (nativeHeatChildBandMomentGenerator U hU hvol M.nu
        (Annealed.sigmaBar M m) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 K M m bands P L
        (v := v) hA T k θ) (Icc 0 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (nativeHeatChildBandMoment U hU hvol M.nu
          (Annealed.sigmaBar M m) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1 K M m bands P L hA T k θ)
          (nativeHeatChildBandMomentGenerator U hU hvol M.nu
            (Annealed.sigmaBar M m) M.nu_pos
            (Annealed.sigmaBar_characterization M m).1 K M m bands P L
            (v := v) hA T k θ t) t)
    exact hderiv k hk

end ASDExplicitGamma.Native
