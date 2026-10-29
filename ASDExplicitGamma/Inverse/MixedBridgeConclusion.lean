module

public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.ParentGap
public import ASDExplicitGamma.Inverse.MixedBridgeRootTheta
public import ASDExplicitGamma.Inverse.MixedBridgeDirectionalLocalTheta
public import ASDExplicitGamma.Scalar.MixedSourceCarriers

/-! The actual-law `IN-MIXED-BRIDGE` conclusion, assembled from the root
OLD-Theta row, parent-gap rows, and the local first-corrector identity. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Algsuperdiff.Section3 Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Native ASDExplicitGamma.Scalar
open ASDExplicitGamma.Main
open ASDExplicitGamma.Triadic
open scoped ENNReal

noncomputable section

/-- Every depth of the root raw weak trace is in `L²` under the original
cutoff law, by the source-scale-zero case of the actual local profile. -/
theorem mixed_bridge_root_trace_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) :
    MemLp (rawWeakTraceSequence M m (originCube 2 m) t · j) 2
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let Q := originCube 2 m
  have hQ : Q ∈ descendantsAtDepth Q 0 := by
    simp [Q, Homogenization.descendantsAtDepth_zero]
  have hprofile := mixed_bridge_local_trace_profile
    M h hM hγ N hpast m hm t ht 0 (by omega) Q hQ j
  rw [memLp_iff]
  calc
    eLpNorm (rawWeakTraceSequence M m (originCube 2 m) t · j) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
        simpa [mixedDepthTraceAverage, Q] using hprofile
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The output history cap is the actual `L²` norm of the root weak
history. Off the insertion interval it is set to zero, where no source row is
requested. -/
noncomputable def mixedBridgeRootHistoryCap
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) : ℝ → ℝ := fun t =>
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then
    ‖mixedOldWeakHistory M m (originCube 2 m) t
      (mixed_bridge_root_trace_memLp M h hM hγ N hpast m hm t ht)‖
  else 0

/-- The complete mixed-bridge package on the actual cutoff
law. The primal and reciprocal carriers are the square roots of the exact
paired source energies, and the local first-corrector carrier is the actual
one from `BridgeObservables` (proved identically zero here). -/
theorem mixed_bridge_root_package
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) :
    InMixedBridgeConclusion M h m
      (mixed_bridge_root_trace_memLp M h hM hγ N hpast m hm)
      (fun t ω => mixedBridgeV M m t ω)
      (fun t ω => mixedBridgeG M m t ω)
      (fun t ω => mixedBridgeVl M m t ω)
      (mixedBridgeRootHistoryCap M h hM hγ N hpast m hm)
      (by
        intro t ht
        simp [mixedBridgeRootHistoryCap, ht]) := by
  classical
  change ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → _
  intro t ht
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hroot := mixed_root_old_theta_row M h hM hγ N hpast m hm t ht
  have hparent := in_parent_gap M h hM hγ N hpast m hm t ht
  have hBcarrier (ω : Cutoff.CutoffSample 2) :
      mixedGlobalHistoryMax M m t ω = mixedBridgeBstar M m t ω := by
    dsimp [mixedGlobalHistoryMax, mixedObserverRoots,
      mixedBridgeBstar]
    rw [← mixed_bridge_observer_roots_eq_bank_union m,
      ← mixed_bridge_bstar_eq_bank_finite_history M m t ht ω]
    exact ENNReal.toReal_ofReal (mixed_bridge_bstar_nonneg M m t ω)
  have hxi : mixedBridgeXi M h m t = mixedXi M h m t := by
    change mixedBridgeXiPre M + mixedBridgeReserve M +
      t * mixedBridgeXiSlope M h m = _
    rw [mixed_bridge_xi_slope_eq_source_series]
    simp [mixedBridgeXiPre, mixedBridgeReserve,
      mixedXi, mixedXiPreCap, mixedXiSlope]
  have hanchor (ω : Cutoff.CutoffSample 2) :
      mixedOldFrameTrace M m t ω = mixedBridgeAnchorTrace M m t ω := by
    rfl
  have hanchorMean :
      (∫ ω, mixedOldFrameTrace M m t ω ∂μ) =
        mixedBridgeAnchorMean M m t := by
    unfold mixedBridgeAnchorMean
    rw [show (fun ω => mixedOldFrameTrace M m t ω) =
      (fun ω => mixedBridgeAnchorTrace M m t ω) from funext hanchor]
  have hV2 (ω : Cutoff.CutoffSample 2) :
      mixedBridgeV M m t ω ^ 2 = mixedBridgeV2 M m t ω := by
    simpa [mixedBridgeV] using Real.sq_sqrt (hparent.1 ω)
  have hG2nonneg (ω : Cutoff.CutoffSample 2) :
      0 ≤ mixedBridge M m t ω := by
    unfold mixedBridge
    positivity
  have hG2 (ω : Cutoff.CutoffSample 2) :
      mixedBridgeG M m t ω ^ 2 = mixedBridge M m t ω := by
    simpa [mixedBridgeG] using Real.sq_sqrt (hG2nonneg ω)
  have hVl2 (ω : Cutoff.CutoffSample 2) :
      mixedBridgeVl M m t ω ^ 2 = 0 := by
    rw [mixedBridgeVl, mixed_bridge_vl2_zero]
    simp
  have hxi0 : 0 ≤ mixedXi M h m t := by
    have htheta : 0 ≤ theta M := by
      unfold theta
      exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
    have hpre : 0 ≤ (inSourceXi5Pre : ℝ) := by
      norm_num [inSourceXi5Pre, ASDExplicitGamma.Numerics.Native.nativeSource5Result]
    have hslope : 0 ≤ mixedXiSlope M h m := by
      unfold mixedXiSlope
      apply tsum_nonneg
      intro r
      have hw : 0 ≤ inSourceOldEnergyHistoryWeight M r := by
        unfold inSourceOldEnergyHistoryWeight
        have hα := inverse_history_discount_range
        have hpref : 0 ≤ 1 - inverseHistoryDiscount ^ 2 := by
          nlinarith [hα.1, hα.2]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg hpref (pow_nonneg hα.1.le _))
            (by norm_num : 0 ≤ (3683 / 2500 : ℝ)))
          (Real.rpow_nonneg (by norm_num) _)
      have hs : 0 ≤ inSourceMeanSlopeActual M h m r := by
        unfold inSourceMeanSlopeActual
        exact le_max_left _ _
      exact mul_nonneg hw hs
    unfold mixedXi mixedXiPreCap
    exact add_nonneg
      (add_nonneg (mul_nonneg htheta hpre)
        (mul_nonneg (by norm_num) htheta))
      (mul_nonneg ht.1 hslope)
  have hHistoryNonneg :
      0 ≤ mixedBridgeRootHistoryCap M h hM hγ N hpast m hm t := by
    by_cases hti : t ∈ Set.Icc (0 : ℝ) 1
    · simp [mixedBridgeRootHistoryCap, hti]
    · simp [mixedBridgeRootHistoryCap, hti]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    exact (hroot k).2
  · intro k
    have hrow := hparent.2.1 k.val (by omega)
    have hrowIntegrand (ω : Cutoff.CutoffSample 2) :
        mixedGlobalHistoryMax M m t ω ^ k.val * mixedBridgeV M m t ω ^ 2 =
          mixedBridgeBstar M m t ω ^ k.val * mixedBridgeV2 M m t ω := by
      rw [hBcarrier ω, hV2 ω]
    have hrowIntegral :
        (∫ ω, mixedGlobalHistoryMax M m t ω ^ k.val *
          mixedBridgeV M m t ω ^ 2 ∂μ) =
        (∫ ω, mixedBridgeBstar M m t ω ^ k.val *
          mixedBridgeV2 M m t ω ∂μ) :=
      integral_congr_ae (Filter.Eventually.of_forall hrowIntegrand)
    rw [hrowIntegral, ← hxi, hanchorMean]
    simpa [mainBeta, mainBetaOld] using hrow.2
  · intro k
    have hrow := hparent.2.2 k.val (by omega)
    have hrowIntegrand (ω : Cutoff.CutoffSample 2) :
        mixedGlobalHistoryMax M m t ω ^ k.val *
          (mixedBridgeV M m t ω ^ 2 + mixedBridgeG M m t ω ^ 2) =
        mixedBridgeBstar M m t ω ^ k.val *
          (mixedBridgeV2 M m t ω + mixedBridge M m t ω) := by
      rw [hBcarrier ω, hV2 ω, hG2 ω]
    have hrowIntegral :
        (∫ ω, mixedGlobalHistoryMax M m t ω ^ k.val *
          (mixedBridgeV M m t ω ^ 2 + mixedBridgeG M m t ω ^ 2) ∂μ) =
        (∫ ω, mixedBridgeBstar M m t ω ^ k.val *
          (mixedBridgeV2 M m t ω + mixedBridge M m t ω) ∂μ) :=
      integral_congr_ae (Filter.Eventually.of_forall hrowIntegrand)
    rw [hrowIntegral, ← hxi]
    simpa [mainBeta] using hrow.2
  · have hzero :
      (∫ ω, mixedGlobalHistoryMax M m t ω *
        mixedBridgeVl M m t ω ^ 2 ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with ω
      change mixedGlobalHistoryMax M m t ω *
        mixedBridgeVl M m t ω ^ 2 = 0
      rw [hVl2 ω]
      ring
    have hright :
      0 ≤ mainBeta * mixedXi M h m t +
        mainEpsNew * (1 + inverseHistoryDiscount) * mainBeta *
          mixedBridgeRootHistoryCap M h hM hγ N hpast m hm t := by
      have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
      have hε : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
      have hα : 0 ≤ 1 + inverseHistoryDiscount := by
        have hrange := inverse_history_discount_range
        linarith
      exact add_nonneg (mul_nonneg hβ hxi0)
        (mul_nonneg (mul_nonneg (mul_nonneg hε hα) hβ) hHistoryNonneg)
    rw [hzero]
    exact hright

/-- The directional bottom-pair payment, with the same cutoff sample, OLD frame, and depth-five source cell.
The actual-law expectation cap for its dominating local `OLD-Theta` is
`mixed_bridge_local_old_theta_envelope`. -/
theorem mixed_bridge_source_bottom_pair_le_local_old_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ω : Cutoff.CutoffSample 2) :
    Main.mainSourceBottomPairTrace M m t ω ≤
      (1 + inverseHistoryDiscount) *
        mixedOldTheta M m (originCube 2 (m - 5)) t ω := by
  exact main_source_bottom_pair_trace_le_local_old_theta
    M h hM hγ N hpast m hm t ht ω

end

end ASDExplicitGamma.Inverse
