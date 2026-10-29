module

public import ASDExplicitGamma.Gaussian.BandChildIdentities
public import ASDExplicitGamma.Native.HeatCooperativeSystem

/-! # Native cooperative moments along the complete fresh-shell band -/

@[expose] public section

open MeasureTheory Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal

namespace ASDExplicitGamma.Native

/-- The degree-`r` child moment along the actual finite-shell interpolation.
The fresh input is the complete band `bands`, so all children share its full
joint center covariance. -/
noncomputable def nativeHeatChildBandMoment
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (m : ℤ) (bands : Fin b → ℤ)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ)) (r : ℕ) (θ t : ℝ) : ℝ :=
  bandModelBackwardAverage K M m bands P hA
    (((childConstantMap (fun i => closure (U i))).comp L).comp T)
    (childPower U hU hvol ν σ hν hσ r) θ t

/-- The exact cancelled-generator moment along the same finite-band path. -/
noncomputable def nativeHeatChildBandMomentGenerator
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (m : ℤ) (bands : Fin b → ℤ)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ)) (r : ℕ) (θ t : ℝ) : ℝ :=
  if r = 0 then 0 else
    bandModelBackwardAverage K M m bands P hA
      (((childConstantMap (fun i => closure (U i))).comp L).comp T)
      (cancelledGenerator (fun j => T (v j)) P L
        (childConstantMap (fun i => closure (U i)))
        (childPower U hU hvol ν σ hν hσ r) θ) θ t

/-- At the initial point of the backward interpolation, the auxiliary
Gaussian has variance `1 + θ`. The same-curve value is therefore the actual
finite-band source average at heat time `1 + θ`; this identity keeps the
physical band law and the old field on their common cutoff probability space. -/
theorem nativeHeatChildBandMoment_start_eq_actualBandAverage
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (m : ℤ) (bands : Fin b → ℤ)
    (hbands : ∀ i, m < bands i)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ)) {θ : ℝ} (_hθ : 0 < θ)
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K bands) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)) (r : ℕ) :
    nativeHeatChildBandMoment U hU hvol ν σ hν hσ K M m bands P L hA T
        r θ 0 =
      bandModelAverage K M m bands P
        ((childConstantMap (fun i => closure (U i))).comp L)
        (childPower U hU hvol ν σ hν hσ r) (1 + θ) := by
  classical
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isCompact_iff_compactSpace.mpr inferInstance)
  let I : (Fin n → ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)) :=
    childConstantMap (fun i => closure (U i))
  let Φ : (∀ i, C(closure (U i), ℝ)) → ℝ :=
    childPower U hU hvol ν σ hν hσ r
  let S : BandHilbert b →L[ℝ] (∀ i, C(closure (U i), ℝ)) :=
    (I.comp L).comp T
  let μ := (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map P)
  have hΦ := childPower_polynomial U hU hvol ν σ hν hσ r
  have hΦgrowth : HasPolynomialGrowth Φ := by
    obtain ⟨_, C, hC, d, hbound, _, _⟩ := hΦ
    exact ⟨C, hC, d, hbound⟩
  have hback := bandModelBackwardAverage_eq K M ell m hK bands hbands
    hA T hlaw P hA S (Φ := Φ) hΦ.1.continuous hΦgrowth θ
  have hmom (d : ℕ) : Integrable
      (fun x : ∀ i, C(closure (U i), ℝ) => (1 + ‖x‖) ^ d) μ := by
    have hm := polynomial_moments_map _
      (integrable_polynomial_olderFieldLaw K M ell m hK) P
    exact hm d
  let Z := gaussianSeriesLimitE hA S
  have hZ : StronglyMeasurable Z := stronglyMeasurable_gaussianSeriesLimitE hA S
  have hZm (d : ℕ) : Integrable (fun ω => (1 + ‖Z ω‖) ^ d)
      standardGaussianInfinitePi := by
    have hz : MemLp Z ((d + 2 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi := by
      convert memLp_gaussianSeriesLimitE hA S (p := d + 2)
        (by exact_mod_cast (show 2 ≤ d + 2 by omega)) using 1
      simp [ENNReal.ofReal_add]
    exact integrable_one_add_norm_pow_of_memLp hz
  let a : ℝ := Real.sqrt ((1 + θ) * (1 - (0 : ℝ)))
  have hscaled := integrable_scaled_moments standardGaussianInfinitePi Z hZ hZm a
  have hGcont : Continuous (backwardTest hA S Φ θ 0) :=
    continuous_integral_translate standardGaussianInfinitePi
      (fun ω => a • Z ω) (hZ.const_smul a) hscaled hΦ.1.continuous hΦgrowth
  have hGgrowth : HasPolynomialGrowth (backwardTest hA S Φ θ 0) :=
    polynomial_growth_integral_translate standardGaussianInfinitePi
      (fun ω => a • Z ω) hscaled hΦgrowth
  have hprod (s : ℝ) :
      (∫ p : (∀ i, C(closure (U i), ℝ)) × (ℕ → ℝ),
        backwardTest hA S Φ θ 0
          (p.1 + Real.sqrt s • gaussianSeriesLimitE hA (P.comp T) p.2)
        ∂(μ.prod standardGaussianInfinitePi)) =
      randomBaseHeatAverage hA (P.comp T) μ
        (backwardTest hA S Φ θ 0) s := by
    exact integral_prod _ (integrable_randomBaseHeatIntegrand hA (P.comp T)
      μ hmom _ hGcont.measurable hGgrowth s)
  have hstart :
      backwardAverage hA (P.comp T) hA S μ Φ θ 0 =
        randomBaseHeatAverage hA S μ Φ (1 + θ) := by
    rw [backwardAverage, timeHeatAverage]
    rw [hprod 0]
    simp [randomBaseHeatAverage, gaussianSeriesHeatAverage,
      gaussianSeriesHeatArgument, backwardTest, Real.sqrt_zero,
      zero_smul, S, I, Φ]
  have hforward := bandModelAverage_eq K M ell m hK bands hbands
    hA T hlaw P (I.comp L) Φ hΦ.1.continuous.measurable hΦgrowth (1 + θ)
  change bandModelBackwardAverage K M m bands P hA S Φ θ 0 = _
  rw [show bandModelBackwardAverage K M m bands P hA S Φ θ 0 =
      backwardAverage hA (P.comp T) hA S μ Φ θ 0 by
        simpa [S, μ] using congrFun hback 0]
  rw [hstart, ← hforward]

/-- One band realization gives continuity and the exact cancelled-generator
derivative for every positive child moment. -/
theorem nativeHeat_childBandMoment_regular_of_realization
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (m : ℤ) (bands : Fin b → ℤ)
    (hbands : ∀ i, m < bands i)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (modelBand K bands) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    {θ : ℝ} (hθ : 0 < θ) (r : ℕ) :
    let Φ := childPower U hU hvol ν σ hν hσ r
    let S := ((childConstantMap (fun i => closure (U i))).comp L).comp T
    let F := bandModelBackwardAverage K M m bands P hA S Φ θ
    let D := bandModelBackwardAverage K M m bands P hA S
      (cancelledGenerator (fun j => T (v j)) P L
        (childConstantMap (fun i => closure (U i))) Φ θ) θ
    ContinuousOn F (Icc 0 1) ∧ ContinuousOn D (Icc 0 1) ∧
      (∀ t ∈ Ioo 0 1, HasDerivAt F (D t) t) := by
  classical
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isCompact_iff_compactSpace.mpr inferInstance)
  let X := ∀ i, C(closure (U i), ℝ)
  let P : C(K, ℝ) →L[ℝ] X := P
  let L : C(K, ℝ) →L[ℝ] (Fin n → ℝ) := L
  let I : (Fin n → ℝ) →L[ℝ] X :=
    childConstantMap (fun i => closure (U i))
  let Φ : X → ℝ := childPower U hU hvol ν σ hν hσ r
  let S : BandHilbert b →L[ℝ] X := (I.comp L).comp T
  let older := (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).map P)
  have holder : ∀ d : ℕ, Integrable (fun z : X => (1 + ‖z‖) ^ d) older := by
    have hmom := polynomial_moments_map _
      (integrable_polynomial_olderFieldLaw K M ell m hK) P
    exact hmom
  have hΦpoly : HasPolynomiallyBoundedC2Derivatives Φ := by
    simpa [Φ] using childPower_polynomial U hU hvol ν σ hν hσ r
  have hgenerator := backwardGenerator_continuous_polynomial hΦpoly
    (fun j => P (T (v j))) (fun j => I (L (T (v j))))
    (summable_sq_norm_gaussianDirections hA (P.comp T))
    (summable_sq_norm_gaussianDirections hA ((I.comp L).comp T)) θ
  have hcancel := generator_cancellation
    (summable_sq_norm_gaussianDirections hA T) P L I hΦpoly.1 θ
  have hcancelRegular :
      Continuous (cancelledGenerator (fun j => T (v j)) P L I Φ θ) ∧
      HasPolynomialGrowth (cancelledGenerator (fun j => T (v j)) P L I Φ θ) := by
    rw [← hcancel]
    exact hgenerator
  have hΦgrowth : HasPolynomialGrowth Φ := by
    obtain ⟨_, C, hC, d, hvalue, _, _⟩ := hΦpoly
    exact ⟨C, hC, d, hvalue⟩
  have hF := bandModelBackwardAverage_eq K M ell m hK bands hbands hA T hlaw
    P hA S hΦpoly.1.continuous hΦgrowth θ
  have hD := bandModelBackwardAverage_eq K M ell m hK bands hbands hA T hlaw
    P hA S hcancelRegular.1 hcancelRegular.2 θ
  have hregular := c1On_cancelledBackwardAverage hA T P L I older holder
    hΦpoly hθ
  rcases hregular with ⟨hFreg, hDreg, hderiv, _, _⟩
  dsimp only [S] at hFreg hDreg hderiv ⊢
  rw [hF, hD]
  exact ⟨hFreg, hDreg, hderiv⟩

end ASDExplicitGamma.Native
