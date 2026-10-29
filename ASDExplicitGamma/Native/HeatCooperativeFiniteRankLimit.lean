module

public import ASDExplicitGamma.Native.HeatCooperativeBandCurve
public import ASDExplicitGamma.Native.HeatFiniteRankLimit

/-! Fixed-operator finite-rank passage for the complete cooperative child
moment curve. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Filter MeasureTheory Set Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped Topology

/-- One actual source-band realization supports the complete cooperative
child-moment curve: its fast finite-rank outer averages converge to the
literal finite-band curve, the auxiliary Gaussian series has its fixed-
operator heat derivative and finite-rank limits, and the finite-band curve
has its exact cancelled-generator derivative. No uniform limit in `ν` or in
the source-band height is asserted here. -/
theorem exists_nativeHeatChildBandMomentCurve_finiteRankLimit
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
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
                (childPower U hU hvol ν σ hν hσ k) θ t)
            (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map P)
            r t) atTop
          (𝓝 (nativeHeatChildBandMoment U hU hvol ν σ hν hσ K M m
            bands P L hA T k θ t))) ∧
      (∀ k : ℕ, ∀ x s, 0 < s →
        HasDerivAt (gaussianSeriesHeatAverage hA
          (((childConstantMap (fun i => closure (U i))).comp L).comp T)
          (childPower U hU hvol ν σ hν hσ k) x)
          ((1 / 2 : ℝ) * gaussianSeriesHeatTraceAverage hA
            (((childConstantMap (fun i => closure (U i))).comp L).comp T)
            (childPower U hU hvol ν σ hν hσ k) x s) s ∧
        Tendsto (fun r => gaussianFastHeatAverage hA
          (((childConstantMap (fun i => closure (U i))).comp L).comp T)
          (childPower U hU hvol ν σ hν hσ k) x r s) atTop
          (𝓝 (gaussianSeriesHeatAverage hA
            (((childConstantMap (fun i => closure (U i))).comp L).comp T)
            (childPower U hU hvol ν σ hν hσ k) x s)) ∧
        Tendsto (fun r => gaussianFastHeatTraceAverage hA
          (((childConstantMap (fun i => closure (U i))).comp L).comp T)
          (childPower U hU hvol ν σ hν hσ k) x r s) atTop
          (𝓝 (gaussianSeriesHeatTraceAverage hA
            (((childConstantMap (fun i => closure (U i))).comp L).comp T)
            (childPower U hU hvol ν σ hν hσ k) x s))) ∧
      (∀ k : ℕ, 1 ≤ k →
        ContinuousOn (nativeHeatChildBandMoment U hU hvol ν σ hν hσ K M m
          bands P L hA T k θ) (Icc 0 1) ∧
        ContinuousOn (nativeHeatChildBandMomentGenerator U hU hvol ν σ hν hσ
          K M m bands P L (v := v) hA T k θ) (Icc 0 1) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1,
          HasDerivAt (nativeHeatChildBandMoment U hU hvol ν σ hν hσ K M m
            bands P L hA T k θ)
            (nativeHeatChildBandMomentGenerator U hU hvol ν σ hν hσ
              K M m bands P L (v := v) hA T k θ t) t)) := by
  classical
  obtain ⟨T, v, hA, hlaw⟩ :=
    exists_modelBand_realization K M h hM bands hbandsInj
  let I : (Fin n → ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)) :=
    childConstantMap (fun i => closure (U i))
  let S : BandHilbert b →L[ℝ] (∀ i, C(closure (U i), ℝ)) :=
    (I.comp L).comp T
  let μ := (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map P)
  refine ⟨T, v, hA, hlaw, ?_, ?_, ?_⟩
  · intro k t ht
    have hΦ := childPower_polynomial U hU hvol ν σ hν hσ k
    have hG := backwardTest_regularity hA S hΦ hθ
    have hslice := hG.field_growth ht
    have hconv := nativeHeat_bandFastAverage_tendsto K M ell m hK
      bands hbands hA T hlaw P P (backwardTest hA S
        (childPower U hU hvol ν σ hν hσ k) θ t) hslice t
    simpa [μ, I, S, nativeHeatChildBandMoment,
      bandModelBackwardAverage] using hconv
  · intro k x s hs
    exact nativeHeat_finiteRankPassage hA
      (((childConstantMap (fun i => closure (U i))).comp L).comp T)
      (childPower U hU hvol ν σ hν hσ k)
      (childPower_polynomial U hU hvol ν σ hν hσ k) x hs
  · intro k hk
    have hregular := nativeHeat_childBandMoment_regular_of_realization
      U hU hvol ν σ hν hσ K M m bands hbands P L (v := v) hA T hlaw hθ k
    rcases hregular with ⟨hF, hD, hderiv⟩
    have hk0 : k ≠ 0 := by omega
    have hMomentEq : nativeHeatChildBandMoment U hU hvol ν σ hν hσ
        K M m bands P L hA T k θ =
          (fun t => bandModelBackwardAverage K M m bands P hA
            (((childConstantMap (fun i => closure (U i))).comp L).comp T)
            (childPower U hU hvol ν σ hν hσ k) θ t) := by
      funext t
      rfl
    have hGeneratorEq : nativeHeatChildBandMomentGenerator U hU hvol ν σ
        hν hσ K M m bands P L (v := v) hA T k θ =
          (fun t => bandModelBackwardAverage K M m bands P hA
            (((childConstantMap (fun i => closure (U i))).comp L).comp T)
            (cancelledGenerator (fun j => T (v j)) P L
              (childConstantMap (fun i => closure (U i)))
              (childPower U hU hvol ν σ hν hσ k) θ) θ t) := by
      funext t
      simp [nativeHeatChildBandMomentGenerator, hk0]
    refine ⟨?_, ?_, ?_⟩
    · change ContinuousOn (bandModelBackwardAverage K M m bands P hA
        (((childConstantMap (fun i => closure (U i))).comp L).comp T)
        (childPower U hU hvol ν σ hν hσ k) θ) (Icc 0 1) at hF
      exact hF
    · rw [hGeneratorEq]
      exact hD
    · intro t ht
      have hrow := hderiv t ht
      rw [hMomentEq, hGeneratorEq]
      exact hrow

end ASDExplicitGamma.Native
