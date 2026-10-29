module

public import ASDExplicitGamma.Main.EnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Numerics.Native.Source5

/-! The explicit `mainEnvelopeXi` bound on each depth-five source cell. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
  ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.MainReturn ASDExplicitGamma.Numerics.Native
  ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The completed-root row remains available as a helper for MA-ENVELOPE-XI;
the source node itself is the depth-five local theorem below. -/
theorem main_envelope_xi_actual_law
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ k : Fin 4,
      (∫ ω, mixedGlobalHistoryMax M m t ω ^ k.val *
        mixedOldTheta M m (originCube 2 m) t ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainBeta ^ k.val * mixedXi M h m t := by
  intro t ht k
  exact (mixed_bridge_root_package M h hM hγ N hpast m hm t ht).1 k

/-- The actual-law `OLD-Theta` node on each depth-five source cell, with the
exact explicit inverse envelope and the true OLD frame. -/
theorem main_envelope_xi_depth5_actual_law
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ U : TriadicCube 2,
      U ∈ descendantsAtDepth (originCube 2 m) 5 → ∀ k : Fin 4,
      Integrable (fun ω =>
        mixedGlobalHistoryMax M m t ω ^ k.val *
          mixedOldTheta M m U t ω)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, mixedGlobalHistoryMax M m t ω ^ k.val *
        mixedOldTheta M m U t ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainBeta ^ k.val * mainEnvelopeXi
          ((q3ModelAmplitude M h (m + 1) /
            (Annealed.sigmaBar M m : ℝ)) ^ 2)
          M.gamma mainSourceInversePrefix (theta M) t := by
  intro t ht U hU k
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let v := (q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2
  have hlocal := mixed_bridge_local_weighted_old_theta_xi5
    M h hM hγ N hpast m hm t ht U hU k
  have htheta0 : 0 ≤ theta M := (ASDExplicitGamma.Cold.cold_theta_pos M).le
  have htheta1 : theta M ≤ 1 := ASDExplicitGamma.Cold.cold_theta_le_one M hγ
  have hxi0 : 0 ≤ (inSourceXi5Pre : ℝ) := by
    norm_num [inSourceXi5Pre,
      ASDExplicitGamma.Numerics.Native.nativeSource5Result]
  have hxiCapQ : inSourceXi5Pre ≤
      (140120486781 / 1000000000000 : ℚ) := by
    exact nativeSource5_caps.2.2.1.le
  have hxiCap : (inSourceXi5Pre : ℝ) ≤
      (140120486781 / 1000000000000 : ℝ) := by
    have hxiCapR := (Rat.cast_le (K := ℝ)).2 hxiCapQ
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
      Rat.cast_one] using hxiCapR
  have hprefixQ : (140120486781 / 1000000000000 : ℚ) ≤
      observer1Panel0Data.initialInverseMean - (1 / 10 ^ 12 : ℚ) := by
    decide +kernel
  have hprefix : (140120486781 / 1000000000000 : ℝ) ≤
      mainSourceInversePrefix := by
    change (140120486781 / 1000000000000 : ℝ) ≤
      (observer1Panel0Data.initialInverseMean : ℝ) - (1 / 10 ^ 12 : ℝ)
    have hprefixR := (Rat.cast_le (K := ℝ)).2 hprefixQ
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_one] using hprefixR
  have hpreCap : mixedXiPreCap M ≤ mainSourceInversePrefix := by
    rw [mixedXiPreCap]
    calc
      theta M * (inSourceXi5Pre : ℝ) ≤
          1 * (inSourceXi5Pre : ℝ) :=
        mul_le_mul_of_nonneg_right htheta1 hxi0
      _ = (inSourceXi5Pre : ℝ) := by ring
      _ ≤ (140120486781 / 1000000000000 : ℝ) := hxiCap
      _ ≤ mainSourceInversePrefix := hprefix
  have hslope := mixed_bridge_local_slope_main_chi
    M h hM hγ N hpast m hm
  have htimeSlope : t * mixedBridgeLocalSlope M h m ≤
      t * mainChi v M.gamma :=
    mul_le_mul_of_nonneg_left hslope ht.1
  have hinside :
      mixedXiPreCap M + (1 / 10 ^ 12 : ℝ) * theta M +
          t * mixedBridgeLocalSlope M h m ≤
        mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t := by
    calc
      _ ≤ mainSourceInversePrefix + (1 / 10 ^ 12 : ℝ) * theta M +
            t * mainChi v M.gamma :=
          add_le_add (add_le_add hpreCap le_rfl) htimeSlope
      _ = mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t := rfl
  have hBcarrier (ω : CutoffSample 2) :
      mixedGlobalHistoryMax M m t ω = mixedBridgeBstar M m t ω := by
    dsimp [mixedGlobalHistoryMax, mixedObserverRoots,
      mixedBridgeBstar]
    rw [← mixed_bridge_observer_roots_eq_bank_union m,
      ← mixed_bridge_bstar_eq_bank_finite_history M m t ht ω]
    exact ENNReal.toReal_ofReal
      (mixed_bridge_bstar_nonneg M m t ω)
  have hcarrierReverse :
      (fun ω => mixedBridgeBstar M m t ω ^ k.val *
        mixedOldTheta M m U t ω) =ᵐ[μ]
      (fun ω => mixedGlobalHistoryMax M m t ω ^ k.val *
        mixedOldTheta M m U t ω) := by
    filter_upwards with ω
    rw [hBcarrier ω]
  have htargetInt : Integrable
      (fun ω => mixedGlobalHistoryMax M m t ω ^ k.val *
        mixedOldTheta M m U t ω) μ := hlocal.1.congr hcarrierReverse
  have hIntegralEq :
      (∫ ω, mixedGlobalHistoryMax M m t ω ^ k.val *
        mixedOldTheta M m U t ω ∂μ) =
      ∫ ω, mixedBridgeBstar M m t ω ^ k.val *
        mixedOldTheta M m U t ω ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    rw [hBcarrier ω]
  refine ⟨htargetInt, ?_⟩
  rw [hIntegralEq]
  calc
    _ ≤ (14103 / 10000 : ℝ) ^ k.val *
          (mixedXiPreCap M + (1 / 10 ^ 12 : ℝ) * theta M +
            t * mixedBridgeLocalSlope M h m) := hlocal.2
    _ ≤ mainBeta ^ k.val *
          mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t := by
      have hscale := mul_le_mul_of_nonneg_left hinside
        (pow_nonneg (by norm_num : 0 ≤ (14103 / 10000 : ℝ)) k.val)
      simpa [mainBeta] using hscale

end ASDExplicitGamma.Main
