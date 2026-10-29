module

public import ASDExplicitGamma.Scalar.DefectOldMaximizerDirectional

/-! The directional correlated moment `E[B² T] <= β² ξ / 2` for any pathwise quantity `T`
dominated by the directional inverse-weighted pair-charge series (generic form of
`scalar_directional_moment`). -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Triadic Variational Native Inverse Gaussian
  Algsuperdiff.Section3 Numerics.Inverse ASDExplicitGamma.Main
open scoped ENNReal BigOperators
attribute [local irreducible] Homogenization.descendantsAtDepth
noncomputable section

theorem dir_series_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (Q : TriadicCube 2) (hQ : Q.scale = m + 129) (e : Vec 2) (he : vecNormSq e = 1)
    :
    Integrable (fun ω => bhist M m Q 134 ω ^ 2 * ∑' j : ℕ,
      (1 - Scalar.inverseHistoryDiscount ^ 2) * Scalar.inverseHistoryDiscount ^ (2 * j) *
        depthMax M m Q ω (134 + j) * dirX M m Q e ω j)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, bhist M m Q 134 ω ^ 2 * ∑' j : ℕ,
      (1 - Scalar.inverseHistoryDiscount ^ 2) * Scalar.inverseHistoryDiscount ^ (2 * j) *
        depthMax M m Q ω (134 + j) * dirX M m Q e ω j
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (14103 / 10000 : ℝ) ^ 2 * xi'' M h m / 2 := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hα := Scalar.inverse_history_discount_range
  have hpast' : ∀ n < m, nativeInductionState M h n := fun n hn => hpast n hn.le
  have hpast'' : ∀ n < m + 1, nativeInductionState M h n := fun n hn => hpast n (by omega)
  have hbank := bank_B M h hM hγ m hpast' Q hQ
  have hdepth := fun j => depth_bank M h hM hγ m hpast' Q hQ j
  choose ee he_meas he0 he128 hesplit hele using hdepth
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : (0 : ℝ) ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
  have hCnn (j : ℕ) : 0 ≤ theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 *
      (3 : ℝ) ^ (6 * gammaZero * j) := by positivity
  have hrnn (j : ℕ) : 0 ≤ 5 * inverseBankDepthReserve .localInverse M j := by
    unfold inverseBankDepthReserve inverseBankReserve bankDepthFrame; positivity
  have hbnn (j : ℕ) : 0 ≤ mixedBridgeOldInverseBaseline M j := by
    dsimp [mixedBridgeOldInverseBaseline]; positivity
  have hD0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ depthMax M m Q ω (134 + j) :=
    lemmaVInverseDepthMax_nonneg _ _ _
  have hXle (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      dirX M m Q e ω j ≤ rawWeakTraceSequence M m Q 0 ω (134 + j) := by
    have := dirX_le M m Q e ω j
    rwa [he, one_mul] at this
  have hXm (j : ℕ) : AEStronglyMeasurable (fun ω => dirX M m Q e ω j) μ := by
    unfold dirX descendantsAverage
    refine AEStronglyMeasurable.const_mul ?_ _
    exact Finset.aestronglyMeasurable_fun_sum _ (fun R _ =>
      (smooth_feedback_cell_pair_charge_integrable M m R e).aestronglyMeasurable)
  have hA := rare_assembly μ Scalar.inverseHistoryDiscount (5 / 10 ^ 24) 2 (by norm_num)
    hα.1.le hα.2.le (by norm_num) (by norm_num)
    (fun ω => bhist M m Q 134 ω) (fun ω => max (bhist M m Q 134 ω - 14103 / 10000) 0)
    (fun j ω => dirX M m Q e ω j)
    (fun j ω => depthMax M m Q ω (134 + j)) ee
    (fun j => mixedBridgeOldInverseBaseline M j)
    (fun j => 5 * inverseBankDepthReserve .localInverse M j)
    (fun j => theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j))
    (3683 / 2500)
    (fun ω => Bhist_nonneg M m Q 134 ω)
    (Bhist_measurable M m Q).aestronglyMeasurable hbank.1
    (Filter.Eventually.of_forall (fun ω => by
      have := le_max_left (bhist M m Q 134 ω - 14103 / 10000) 0
      linarith))
    (fun ω => le_max_right _ _)
    (((Bhist_measurable M m Q).sub_const _).max measurable_const).aestronglyMeasurable
    hbank.2
    (fun j ω => dirX_nonneg M m Q e ω j)
    hXm
    (fun j => (eLpNorm_mono_enorm_ae (hXm j) (Filter.Eventually.of_forall
      (fun ω => by
        rw [Real.enorm_of_nonneg (dirX_nonneg M m Q e ω j),
          Real.enorm_of_nonneg (raw_weak_trace_sequence_nonneg M m Q 0
            ⟨le_rfl, zero_le_one⟩ ω _)]
        exact ENNReal.ofReal_le_ofReal (hXle j ω)))).trans
      (scalar_trace_L2 M h hM hγ m hpast Q hQ j))
    hCnn
    hD0 (fun j => (depthMax_measurable M m Q (134 + j)).aestronglyMeasurable)
    he0 (fun j => (he_meas j).aestronglyMeasurable) he128 hrnn hbnn
    (fun j => by
      have h1 := alpha_baseline_le M hγ j
      have : Scalar.inverseHistoryDiscount ^ j * mixedBridgeOldInverseBaseline M j =
          (3683 / 2500 : ℝ) * (Scalar.inverseHistoryDiscount ^ j *
            (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by
        simp only [mixedBridgeOldInverseBaseline]; ring
      rw [this]
      nlinarith [h1])
    (ae_all_iff.mpr (fun j => by
      filter_upwards [hesplit j] with ω hω
      simpa [mixedBridgeOldInverseBaseline] using hω))
    (fun j ω => alpha_depth_le_B M m Q ω j)
    (fun j ω => (mul_le_mul_of_nonneg_left (hele j ω) (pow_nonneg hα.1.le j)).trans
      (alpha_depth_le_B M m Q ω j))
    (Filter.Eventually.of_forall (fun ω =>
      Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hα.1.le j)
          (dirX_nonneg M m Q e ω j))
        (fun j => mul_le_mul_of_nonneg_left (hXle j ω) (pow_nonneg hα.1.le j))
        (traceSeries_summable M m Q ω)))
    (global_numeric M hγ).1 (local_numeric M hγ).1
    (by
      have hsrc := (mixed_bridge_local_mean_transport M h hM hγ (m + 1) hpast'' m
        (by omega) 0 ⟨le_rfl, zero_le_one⟩).1
      have hs2 := hsrc.mul_left (1 / 2 : ℝ)
      refine hs2.congr (fun j => ?_)
      rw [dirX_mean, he, (scalar_trace_mean M h hM hγ m hpast Q hQ j).2]
      simp only [mixedBridgeLocalWeight]
      ring)
  obtain ⟨hAint, hAle⟩ := hA
  have hsrc := (mixed_bridge_local_mean_transport M h hM hγ (m + 1) hpast'' m
    (by omega) 0 ⟨le_rfl, zero_le_one⟩).2
  have hbaseEq : (∑' j : ℕ, (1 - Scalar.inverseHistoryDiscount ^ 2) *
      Scalar.inverseHistoryDiscount ^ (2 * j) * mixedBridgeOldInverseBaseline M j *
        ∫ ω, dirX M m Q e ω j ∂μ) =
      (1 / 2 : ℝ) * ∑' j : ℕ, mixedBridgeLocalWeight M j *
        inSourceMeanActual M m (5 + j) 0 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [dirX_mean, he, (scalar_trace_mean M h hM hγ m hpast Q hQ j).2]
    simp only [mixedBridgeLocalWeight]
    ring
  rw [hbaseEq] at hAle
  have hG := (global_numeric M hγ).2
  have hL := local_numeric_small M hγ
  have hpre := preCap_le_prefix M hγ
  have hxi : xi'' M h m = mainSourceInversePrefix + (1 / 10 ^ 12 : ℝ) * theta M := by
    simp only [xi'', mainEnvelopeXi]; ring
  have hsrc' : (∑' j : ℕ, mixedBridgeLocalWeight M j * inSourceMeanActual M m (5 + j) 0) ≤
      mainSourceInversePrefix := by
    have := hsrc
    simp only [zero_mul, add_zero] at this
    exact this.trans hpre
  have hβ2 : (0 : ℝ) ≤ (14103 / 10000) ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hsrc' hβ2
  have hk : (1 / (4 * 10 ^ 12 : ℝ)) + (14103 / 10000 : ℝ) ^ 2 * (1 / 10 ^ 30 : ℝ) ≤
      (14103 / 10000 : ℝ) ^ 2 * (1 / (2 * 10 ^ 12) : ℝ) := by norm_num
  have hk' := mul_le_mul_of_nonneg_right hk htheta
  have hbound : (∫ ω, bhist M m Q 134 ω ^ 2 * ∑' j : ℕ, (1 - Scalar.inverseHistoryDiscount ^ 2) *
      Scalar.inverseHistoryDiscount ^ (2 * j) * depthMax M m Q ω (134 + j) *
        dirX M m Q e ω j ∂μ) ≤ (14103 / 10000 : ℝ) ^ 2 * xi'' M h m / 2 := by
    rw [hxi]
    nlinarith [hAle, hk', h3, hG, hL]
  exact ⟨hAint, hbound⟩

end
end ASDExplicitGamma.Scalar
