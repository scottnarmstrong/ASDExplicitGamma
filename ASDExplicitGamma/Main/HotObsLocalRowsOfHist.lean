module

public import ASDExplicitGamma.Main.HotObsLocalRows

/-! Successors of `HotObsLocalRows` declarations with the history envelope as a parameter `Hfun`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Cold ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Successor of `mixed_bridge_local_parent_gap_rows''` with the history envelope `Hfun`. -/
theorem mixed_bridge_local_parent_gap_rows_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hscale : U.scale = m - ((5 : ℕ) : ℤ))
    (hUObserver : U ∈ bankObserverRoots (originCube 2 (m + 40)) 5)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    let B : Cutoff.CutoffSample 2 → ℝ := mixedGlobalHistoryMax M m t
    let V : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVLocal M m U t
    let G : Cutoff.CutoffSample 2 → ℝ := mixedBridgeGLocal M m U t
    let Vl : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVlLocal M m U t
    let f_U := ∫ ω, rawCubeFourLoadTrace M m U t ω ∂μ
    Integrable (fun ω => V ω ^ 2) μ ∧
    (∫ ω, V ω ^ 2 ∂μ) ≤ xi - mainBetaOld * f_U ∧
    (∀ k : Fin 4,
      Integrable (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ ∧
      (∫ ω, B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ∂μ) ≤
        2 * mainBeta ^ k.val * xi) ∧
    Integrable (fun ω => B ω * G ω ^ 2) μ ∧
    (∫ ω, B ω * G ω ^ 2 ∂μ) ≤ 2 * mainBeta * xi ∧
    Integrable (fun ω => B ω * Vl ω ^ 2) μ ∧
    (∫ ω, B ω * Vl ω ^ 2 ∂μ) ≤
      mainBeta * xi + mainEpsNew * mainD * mainBeta *
        Hfun t := by
  classical
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let v := (q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2
  let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
  let B : Cutoff.CutoffSample 2 → ℝ := mixedGlobalHistoryMax M m t
  let V : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVLocal M m U t
  let G : Cutoff.CutoffSample 2 → ℝ := mixedBridgeGLocal M m U t
  let Vl : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVlLocal M m U t
  let f_U := ∫ ω, rawCubeFourLoadTrace M m U t ω ∂μ

  have hEnvelope := main_envelope_xi_depth5_actual_law'
    M h hM hγ N hpast m hm t ht U hscale
  have hThetaInt : Integrable (mixedOldTheta M m U t) μ := by
    simpa [μ] using (hEnvelope ⟨0, by norm_num⟩).1
  have hBcarrier (ω : Cutoff.CutoffSample 2) :
      B ω = mixedBridgeBstar M m t ω := by
    dsimp [B, mixedGlobalHistoryMax, mixedObserverRoots,
      mixedBridgeBstar]
    rw [← mixed_bridge_observer_roots_eq_bank_union m,
      ← mixed_bridge_bstar_eq_bank_finite_history M m t ht ω]
    exact ENNReal.toReal_ofReal
      (mixed_bridge_bstar_nonneg M m t ω)
  have hBmeas : Measurable B := by
    have heq : B = mixedBridgeBstar M m t := funext hBcarrier
    rw [heq]
    exact parent_gap_bstar_measurable M m t
  have hBnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω := by
    rw [hBcarrier ω]
    exact mixed_bridge_bstar_nonneg M m t ω
  have hVmeas : Measurable (fun ω => V ω ^ 2) := by
    simpa [V] using mixed_bridge_local_v2_measurable' M m U t
  have hGmeas : Measurable (fun ω => G ω ^ 2) := by
    simpa [G] using mixed_bridge_local_measurable' M m U t
  have hThetaNonneg (ω : Cutoff.CutoffSample 2) :
      0 ≤ mixedOldTheta M m U t ω := by
    unfold mixedOldTheta
    apply tsum_nonneg
    intro j
    rw [mixedOldThetaTerm]
    have hcoeff : 0 ≤ mixedOldDepthCoefficient M m t j ω := by
      rw [mixed_old_depth_coefficient_formula]
      change 0 ≤ (3683 / 2500 : ℝ) * (3 : ℝ) ^
        (2 * M.gamma * (j : ℝ)) + positiveSplitRemainder _ _ _
      exact add_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by norm_num) _)) ((positive_split _ _ _).1)
    have hw : 0 ≤ (1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j) :=
      mul_nonneg
        (sub_nonneg.mpr (pow_le_one₀
          Scalar.inverse_history_discount_range.1.le
          Scalar.inverse_history_discount_range.2.le))
        (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
    exact mul_nonneg (mul_nonneg hw hcoeff)
      (raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j)
  have hXiNonneg : 0 ≤ xi := by
    have hpre : 0 ≤ mainSourceInversePrefix := by
      have hbeta : 0 < mainBetaOld / 100 := by norm_num [mainBetaOld]
      exact le_of_lt (lt_trans hbeta mainSourceInversePrefix_gate)
    exact hpre.trans (mainEnvelopeXi_ge_initial (sq_nonneg _)
      M.shellPrefix.gamma_pos.le hγ (ASDExplicitGamma.Cold.cold_theta_pos M).le ht.1)

  have hrows : ∀ᵐ ω ∂μ,
      V ω ^ 2 ≤ mixedOldTheta M m U t ω -
          mainBetaOld * rawCubeFourLoadTrace M m U t ω ∧
      V ω ^ 2 + G ω ^ 2 ≤ 2 * mixedOldTheta M m U t ω := by
    simpa [V, G, μ] using
      mixed_bridge_local_pointwise_rows' M h hM hγ N hpast m hm t ht U hUObserver
  have hTraceLaw := mixed_bridge_local_trace_mean'
    M h hM hγ N hpast m hm t ht 5 le_rfl U hscale 0
  have hTraceInt : Integrable (rawCubeFourLoadTrace M m U t) μ := by
    have hTInt := hTraceLaw.1
    have hEq (ω : Cutoff.CutoffSample 2) :
        mixedDepthTraceAverage M m U t ω 0 =
          rawCubeFourLoadTrace M m U t ω := by
      change Cold.squareCellMean U 0
        (fun C => rawCubeFourLoadTrace M m C.1 t ω) = _
      rw [mixed_bridge_local_squareCellMean_eq_descendantsAverage' U 0
        (fun V => rawCubeFourLoadTrace M m V t ω)]
      simp [descendantsAverage, Homogenization.descendantsAtDepth_zero]
    exact hTInt.congr (Filter.Eventually.of_forall hEq)
  have hGapInt : Integrable
      (fun ω => mixedOldTheta M m U t ω -
        mainBetaOld * rawCubeFourLoadTrace M m U t ω) μ :=
    hThetaInt.sub (hTraceInt.const_mul mainBetaOld)
  have hVInt : Integrable (fun ω => V ω ^ 2) μ := by
    apply hGapInt.mono' hVmeas.aestronglyMeasurable
    filter_upwards [hrows] with ω hω
    have hleft : 0 ≤ V ω ^ 2 := sq_nonneg _
    have hright : 0 ≤ mixedOldTheta M m U t ω -
        mainBetaOld * rawCubeFourLoadTrace M m U t ω := le_trans hleft hω.1
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hω.1
  have hVIntegralBound :
      (∫ ω, V ω ^ 2 ∂μ) ≤ xi - mainBetaOld * f_U := by
    have hmono := integral_mono_ae hVInt hGapInt (by
      filter_upwards [hrows] with ω hω
      exact hω.1)
    have hthetaBound :
        (∫ ω, mixedOldTheta M m U t ω ∂μ) ≤ xi := by
      simpa [μ, xi, v] using (hEnvelope ⟨0, by norm_num⟩).2
    have hgapIntegral :
        (∫ ω, mixedOldTheta M m U t ω -
          mainBetaOld * rawCubeFourLoadTrace M m U t ω ∂μ) ≤
          xi - mainBetaOld * f_U := by
      rw [integral_sub hThetaInt (hTraceInt.const_mul mainBetaOld),
        integral_const_mul]
      exact sub_le_sub_right hthetaBound (mainBetaOld * f_U)
    exact hmono.trans hgapIntegral

  have hPairRows : ∀ k : Fin 4,
      Integrable (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ ∧
      (∫ ω, B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ∂μ) ≤
        2 * mainBeta ^ k.val * xi := by
    intro k
    have hEnv := hEnvelope k
    have hIntegrandMeas : Measurable
        (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) :=
      (hBmeas.pow_const k.val).mul (hVmeas.add hGmeas)
    have hpairInt : Integrable
        (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ := by
      apply (hEnv.1.const_mul 2).mono' hIntegrandMeas.aestronglyMeasurable
      filter_upwards [hrows] with ω hω
      have hpow : 0 ≤ B ω ^ k.val := pow_nonneg (hBnonneg ω) _
      have hleft : 0 ≤ B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) :=
        mul_nonneg hpow (add_nonneg (sq_nonneg _) (sq_nonneg _))
      have hright : 0 ≤ 2 * (B ω ^ k.val * mixedOldTheta M m U t ω) :=
        mul_nonneg (by norm_num) (mul_nonneg hpow (hThetaNonneg ω))
      have hbound : B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ≤
          2 * (B ω ^ k.val * mixedOldTheta M m U t ω) := by
        calc
          _ ≤ B ω ^ k.val * (2 * mixedOldTheta M m U t ω) :=
            mul_le_mul_of_nonneg_left hω.2 hpow
          _ = _ := by ring
      rw [Real.norm_of_nonneg hleft]
      simpa [B] using hbound
    have hpairIntegral := integral_mono_ae hpairInt (hEnv.1.const_mul 2) (by
      filter_upwards [hrows] with ω hω
      have hpow : 0 ≤ B ω ^ k.val := pow_nonneg (hBnonneg ω) _
      calc
        B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ≤
            2 * (B ω ^ k.val * mixedOldTheta M m U t ω) := by
              calc
                _ ≤ B ω ^ k.val * (2 * mixedOldTheta M m U t ω) :=
                  mul_le_mul_of_nonneg_left hω.2 hpow
                _ = _ := by ring
        _ = 2 * (B ω ^ k.val * mixedOldTheta M m U t ω) := rfl)
    have hEnvBound :
        (∫ ω, B ω ^ k.val * mixedOldTheta M m U t ω ∂μ) ≤
          mainBeta ^ k.val * xi := by
      simpa [B, μ, xi, v] using hEnv.2
    refine ⟨hpairInt, ?_⟩
    calc
      _ ≤ 2 * (∫ ω, B ω ^ k.val * mixedOldTheta M m U t ω ∂μ) := by
        simpa only [integral_const_mul] using hpairIntegral
      _ ≤ 2 * (mainBeta ^ k.val * xi) :=
        mul_le_mul_of_nonneg_left hEnvBound (by norm_num)
      _ = 2 * mainBeta ^ k.val * xi := by ring

  have hGInt : Integrable (fun ω => B ω * G ω ^ 2) μ := by
    have hmeas : Measurable (fun ω => B ω * G ω ^ 2) := hBmeas.mul hGmeas
    have hpair := hPairRows ⟨1, by norm_num⟩ |>.1
    apply hpair.mono' hmeas.aestronglyMeasurable
    filter_upwards with ω
    have hleft : 0 ≤ B ω * G ω ^ 2 := mul_nonneg (hBnonneg ω) (sq_nonneg _)
    have hright : 0 ≤ B ω ^ 1 * (V ω ^ 2 + G ω ^ 2) :=
      mul_nonneg (pow_nonneg (hBnonneg ω) 1)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hbound : B ω * G ω ^ 2 ≤ B ω ^ 1 * (V ω ^ 2 + G ω ^ 2) := by
      have hbase : G ω ^ 2 ≤ V ω ^ 2 + G ω ^ 2 := by nlinarith [sq_nonneg (V ω)]
      simpa only [pow_one] using mul_le_mul_of_nonneg_left hbase (hBnonneg ω)
    rw [Real.norm_of_nonneg hleft]
    simpa only [pow_one] using hbound
  have hGIntegralBound :
      (∫ ω, B ω * G ω ^ 2 ∂μ) ≤ 2 * mainBeta * xi := by
    have hmono := integral_mono_ae hGInt
      (hPairRows ⟨1, by norm_num⟩).1 (by
        filter_upwards with ω
        have hbase : G ω ^ 2 ≤ V ω ^ 2 + G ω ^ 2 := by nlinarith [sq_nonneg (V ω)]
        simpa only [pow_one] using mul_le_mul_of_nonneg_left hbase (hBnonneg ω))
    have hpairBound := (hPairRows ⟨1, by norm_num⟩).2
    simpa only [pow_one] using hmono.trans hpairBound

  have hVlZero (ω : CutoffSample 2) : Vl ω ^ 2 = 0 := by
    simp [Vl, mixedBridgeVlLocal, mixed_bridge_local_vl2_zero']
  have hVlInt : Integrable (fun ω => B ω * Vl ω ^ 2) μ := by
    have heq : (fun ω => B ω * Vl ω ^ 2) = fun _ : CutoffSample 2 => 0 := by
      funext ω
      rw [hVlZero ω]
      ring
    rw [heq]
    exact integrable_const 0
  have hVlIntegral : (∫ ω, B ω * Vl ω ^ 2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with ω
    simp [hVlZero ω]
  have hVlBound :
      (∫ ω, B ω * Vl ω ^ 2 ∂μ) ≤
        mainBeta * xi + mainEpsNew * mainD * mainBeta *
          Hfun t := by
    rw [hVlIntegral]
    have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
    have hε : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
    have hAlpha : 0 ≤ mainAlpha :=
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
    have hD : 0 ≤ mainD := by
      dsimp [mainD]
      exact add_nonneg (by norm_num) hAlpha
    have hH : 0 ≤ Hfun t :=
      (le_trans lpNorm_nonneg (hHist t ht).2.2)
    positivity

  refine ⟨hVInt, hVIntegralBound, hPairRows, hGInt, hGIntegralBound,
    hVlInt, hVlBound⟩

end
end ASDExplicitGamma.Main
end
