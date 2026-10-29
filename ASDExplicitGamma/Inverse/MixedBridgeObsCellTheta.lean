module

public import ASDExplicitGamma.Inverse.MixedBridgeObsCellSummability
public import ASDExplicitGamma.Inverse.MixedBridgeLocalBudget
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeRootTheta
public import ASDExplicitGamma.Inverse.ParentGapHolder

/-! The actual-law OLD-Theta row on an arbitrary scale-`m-5` source cell. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Filter Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

private theorem local_nonnegative_series_integral_ae
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (f : I → Ω → ℝ) (C : I → ℝ)
    (hf : ∀ j, Integrable (f j) μ)
    (hn : ∀ j ω, 0 ≤ f j ω)
    (hs : ∀ᵐ ω ∂μ, Summable (fun j => f j ω))
    (hC : Summable C)
    (hb : ∀ j, (∫ ω, f j ω ∂μ) ≤ C j) :
    Integrable (fun ω => ∑' j, f j ω) μ ∧
      (∫ ω, ∑' j, f j ω ∂μ) ≤ ∑' j, C j := by
  classical
  have hI : Summable (fun j => ∫ ω, f j ω ∂μ) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (hn j)) hb hC
  have hm : AEStronglyMeasurable (fun ω => ∑' j, f j ω) μ := by
    apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun s : Finset I => s.aestronglyMeasurable_fun_sum
        (fun j _ => (hf j).1))
    filter_upwards [hs] with ω hω
    exact hω.hasSum
  have hsumENN : ∀ᵐ ω ∂μ,
      ENNReal.ofReal (∑' j, f j ω) = ∑' j, ENNReal.ofReal (f j ω) := by
    filter_upwards [hs] with ω hω
    exact ENNReal.ofReal_tsum_of_nonneg (fun j => hn j ω) hω
  have he :
      (∫⁻ ω, ENNReal.ofReal (∑' j, f j ω) ∂μ) =
        ENNReal.ofReal (∑' j, ∫ ω, f j ω ∂μ) := by
    rw [lintegral_congr_ae hsumENN,
      lintegral_tsum
        (fun j => (hf j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hf _)
      (Filter.Eventually.of_forall (hn _))]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun j => integral_nonneg (hn j)) hI).symm
  have hi : Integrable (fun ω => ∑' j, f j ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm
      (Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun j => hn j ω)))).mp
      (by rw [he]; exact ENNReal.ofReal_ne_top)
  refine ⟨hi, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hf
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] using hI)]
  exact hI.tsum_le_tsum hb hC

private theorem local_weight_nonneg'' (M : ABKModel 2) (j : ℕ) :
    0 ≤ mixedBridgeLocalWeight M j := by
  unfold mixedBridgeLocalWeight mixedBridgeOldInverseBaseline
  have hα := Scalar.inverse_history_discount_range
  have hpref : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    nlinarith [hα.1, hα.2]
  exact mul_nonneg (mul_nonneg hpref
      (pow_nonneg hα.1.le _))
    (mul_nonneg (by norm_num : 0 ≤ (3683 / 2500 : ℝ))
      (Real.rpow_nonneg (by norm_num) _))

private theorem local_profile_nonneg
    (M : ABKModel 2) (j : ℕ) : 0 ≤ rawWeakTraceProfileEnvelope M j := by
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by
    rw [invTrace_coefficient.1]
    positivity
  have hM : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
  unfold rawWeakTraceProfileEnvelope
  positivity

private theorem local_union_depth_block''
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    InverseBankDepthBlockConclusion M .localInverse
      (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
      m (m + 40) (bankPartialInsertionWeights m 1 t) j := by
  have hpastM : ∀ n < m, nativeInductionState M h n := by
    intro n hn
    exact hpast n (hn.trans hm)
  have hQ : (originCube 2 (m + 40)).scale = m + 40 := rfl
  have hw : ∀ k ∈ Finset.Ioc m (m + 40),
      0 ≤ bankPartialInsertionWeights m 1 t k ∧
        bankPartialInsertionWeights m 1 t k ≤ 1 :=
    fun k _ => bank_partial_insertion_weights_bounds m 1 t ht.2 k
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hγ m hpastM).2
  exact (inverse_bank_observer_union_depths M h hM hγ .localInverse
    (originCube 2 (m + 40)) m (m + 40) hQ (by omega)
    (bankPartialInsertionWeights m 1 t) hw 5 le_rfl hpastM hmean j).2

private theorem local_source_weight_le_alpha
    (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (j : ℕ) :
    mixedBridgeLocalWeight M j ≤
      (3683 / 2500 : ℝ) * Scalar.inverseHistoryDiscount ^ j := by
  let α := Scalar.inverseHistoryDiscount
  let q : ℝ := α * (3 : ℝ) ^ (2 * M.gamma)
  have hα := Scalar.inverse_history_discount_range
  have hqeq : q = (3 : ℝ) ^ (-(1 / 4 : ℝ) + 2 * M.gamma) := by
    dsimp [q, α, Scalar.inverseHistoryDiscount]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hq0 : 0 ≤ q := by rw [hqeq]; positivity
  have hexp : -(1 / 4 : ℝ) + 2 * M.gamma < 0 := by
    norm_num [gammaZero] at hγ ⊢
    linarith
  have hq1 : q < 1 := by
    rw [hqeq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hpow : (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
      ((3 : ℝ) ^ (2 * M.gamma)) ^ j := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * M.gamma)) j,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hweight : mixedBridgeLocalWeight M j =
      (1 - α ^ 2) * ((3683 / 2500 : ℝ) * α ^ j) * q ^ j := by
    unfold mixedBridgeLocalWeight mixedBridgeOldInverseBaseline
    rw [hpow]
    dsimp [q, α]
    ring
  have hfactor : 0 ≤ 1 - α ^ 2 ∧ 1 - α ^ 2 ≤ 1 := by
    constructor <;> nlinarith [hα.1, hα.2, sq_nonneg α]
  have hqpow : 0 ≤ q ^ j ∧ q ^ j ≤ 1 :=
    ⟨pow_nonneg hq0 j, pow_le_one₀ hq0 hq1.le⟩
  rw [hweight]
  calc
    (1 - α ^ 2) * ((3683 / 2500 : ℝ) * α ^ j) * q ^ j ≤
        1 * ((3683 / 2500 : ℝ) * α ^ j) * 1 := by
      have hB : 0 ≤ (3683 / 2500 : ℝ) * α ^ j :=
        mul_nonneg (by norm_num) (pow_nonneg hα.1.le j)
      calc
        _ ≤ (1 * ((3683 / 2500 : ℝ) * α ^ j)) * q ^ j :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hfactor.2 hB) hqpow.1
        _ ≤ (1 * ((3683 / 2500 : ℝ) * α ^ j)) * 1 :=
          mul_le_mul_of_nonneg_left hqpow.2 (by positivity)
    _ = (3683 / 2500 : ℝ) * α ^ j := by ring

private theorem local_remainder_trace_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (ε C : ℝ)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hR0 : ∀ ω, 0 ≤ R ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (hRmeas : AEStronglyMeasurable R μ) (hTmeas : AEStronglyMeasurable T μ)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => R ω * T ω) μ ∧
      (∫ ω, R ω * T ω ∂μ) ≤ ε * C := by
  have hconst : eLpNorm (fun _ : Ω => (1 : ℝ)) 128 μ = 1 := by
    rw [eLpNorm_const' (1 : ℝ) (by norm_num) (by norm_num),
      Real.enorm_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    norm_num
  have hconstle : eLpNorm (fun _ : Ω => (1 : ℝ)) 128 μ ≤
      ENNReal.ofReal (1 : ℝ) := by rw [hconst]; norm_num
  have hholder := parent_gap_global_local_rare_term
    (fun _ : Ω => (1 : ℝ)) R T (1 : ℝ) ε C 0 (by omega)
    (fun _ => by norm_num) hR0 hT0
    (aestronglyMeasurable_const) hRmeas hTmeas hconstle hR128 hT2
  have hnonneg (ω : Ω) : 0 ≤ R ω * T ω := mul_nonneg (hR0 ω) (hT0 ω)
  have hbound :
      ∫⁻ ω, ENNReal.ofReal (R ω * T ω) ∂μ ≤ ENNReal.ofReal (ε * C) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (R ω) * ENNReal.ofReal (T ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with ω
        rw [ENNReal.ofReal_mul (hR0 ω)]
      _ = ∫⁻ ω, (ENNReal.ofReal (1 : ℝ)) ^ 0 *
          ENNReal.ofReal (R ω) * ENNReal.ofReal (T ω) ∂μ := by
        congr 1
        ext ω
        norm_num
      _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal (1 : ℝ) ^ 0 * ENNReal.ofReal ε) := by
        simpa using hholder
      _ = ENNReal.ofReal (ε * C) := by
        simp only [ENNReal.ofReal_one, one_pow, one_mul]
        rw [← ENNReal.ofReal_mul hC]
        congr 1
        ring
  have hi : Integrable (fun ω => R ω * T ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hRmeas.mul hTmeas)
      (Filter.Eventually.of_forall hnonneg)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall hnonneg)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hε hC)).mp hbound

private theorem local_rare_series_summable_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (α : ℝ)
    (B : Ω → ℝ) (R T : ℕ → Ω → ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hR0 : ∀ j ω, 0 ≤ R j ω) (hT0 : ∀ j ω, 0 ≤ T j ω)
    (hRbound : ∀ j ω, α ^ j * R j ω ≤ B ω)
    (htrace : ∀ᵐ ω ∂μ, Summable (fun j => α ^ j * T j ω)) :
    ∀ᵐ ω ∂μ, Summable (fun j =>
      ((1 - α ^ 2) * α ^ (2 * j)) * R j ω * T j ω) := by
  filter_upwards [htrace] with ω htrace
  have hlead : Summable (fun j : ℕ =>
      ((1 - α ^ 2) * B ω) * (α ^ j * T j ω)) :=
    htrace.mul_left ((1 - α ^ 2) * B ω)
  have hineq (j : ℕ) :
      ((1 - α ^ 2) * α ^ (2 * j)) * R j ω * T j ω ≤
        ((1 - α ^ 2) * B ω) * (α ^ j * T j ω) := by
    have hTα : 0 ≤ α ^ j * T j ω :=
      mul_nonneg (pow_nonneg hα0 j) (hT0 j ω)
    calc
      _ = (1 - α ^ 2) * (α ^ j * R j ω) * (α ^ j * T j ω) := by ring
      _ ≤ (1 - α ^ 2) * B ω * (α ^ j * T j ω) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hRbound j ω)
            (sub_nonneg.mpr (pow_le_one₀ hα0 hα1))) hTα
      _ = _ := by ring
  have hweight0 (j : ℕ) : 0 ≤ (1 - α ^ 2) * α ^ (2 * j) :=
    mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα0 hα1))
      (pow_nonneg hα0 _)
  have hmajor : Summable (fun j : ℕ =>
      ((1 - α ^ 2) * α ^ (2 * j)) * R j ω * T j ω) := by
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (mul_nonneg (hweight0 j) (hR0 j ω)) (hT0 j ω))
      (fun j => by simpa only [mul_assoc] using hineq j) hlead
  exact hmajor

private theorem local_bank_depth_block
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    InverseBankDepthBlockConclusion M .localInverse
      (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
      m (m + 40) (bankPartialInsertionWeights m 1 t) j :=
  local_union_depth_block'' M h hM hγ N hpast m hm t ht j

/-- The local `OLD-Theta` trace is integrable under the unchanged cutoff law,
and its source-local expectation is bounded by the exact shifted `xi5`
path. The proof keeps frame `m`, the depth-five cell `U`, and source labels
`5+j`. -/
theorem mixed_bridge_obscell_old_theta_local_xi5
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∀ U : TriadicCube 2, U.scale = m - ((5 : ℕ) : ℤ) →
      Integrable (fun ω => mixedOldTheta M m U t ω) μ ∧
      (∫ ω, mixedOldTheta M m U t ω ∂μ) ≤
        mixedBridgeLocalXi5 M h m t := by
  classical
  dsimp only
  intro U hU
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let w : ℕ → ℝ := fun j => (1 - α ^ 2) * α ^ (2 * j)
  let W : ℕ → ℝ := fun j => mixedBridgeLocalWeight M j
  let C : ℕ → ℝ := fun j => rawWeakTraceProfileEnvelope M j
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ :=
    fun j ω => mixedDepthTraceAverage M m U t ω j
  let B : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  let R : ℕ → Cutoff.CutoffSample 2 → ℝ :=
    fun j ω => mixedOldLocalDepthRemainder M m t j ω
  let ε : ℕ → ℝ := fun j => inverseBankDepthReserve .localInverse M j
  let baseTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => W j * T j ω
  let rareTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => w j * R j ω * T j ω
  let baseSeries : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, baseTerm j ω
  let rareSeries : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, rareTerm j ω

  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hα1 : α ≤ 1 := hα.2.le
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω := by
    simpa [B] using mixed_bridge_bstar_nonneg M m t ω
  have hT0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ T j ω := by
    simpa [T, mixedDepthTraceAverage] using
      raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j
  have hprofile (j : ℕ) : eLpNorm (T j) 2 μ ≤ ENNReal.ofReal (C j) := by
    simpa [T, C, μ] using mixed_bridge_obscell_trace_profile
      M h hM hγ N hpast m hm t ht 5 (by omega) U hU j
  have hTmem (j : ℕ) : MemLp (T j) 2 μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt (hprofile j) ENNReal.ofReal_lt_top
  have hTint (j : ℕ) : Integrable (T j) μ :=
    (hTmem j).integrable (by norm_num)
  have hTmeas (j : ℕ) : AEStronglyMeasurable (T j) μ :=
    (hTmem j).aestronglyMeasurable
  have hmean (j : ℕ) :
      (∫ ω, T j ω ∂μ) = inSourceMeanActual M m (5 + j) t := by
    simpa [T, μ] using (mixed_bridge_obscell_trace_mean
      M h hM hγ N hpast m hm t ht 5 (by omega) U hU j).2
  have hsource := mixed_bridge_local_mean_transport
    M h hM hγ N hpast m hm t ht
  have hbaseAe : ∀ᵐ ω ∂μ, Summable (fun j => baseTerm j ω) := by
    have htrace := mixed_bridge_obscell_trace_weighted_summable_ae
      M h hM hγ N hpast m hm t ht U hU
    filter_upwards [htrace] with ω hω
    have hmajor := hω.mul_left (3683 / 2500 : ℝ)
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (local_weight_nonneg'' M j)
        (hT0 j ω))
      (fun j => by
        have hw := local_source_weight_le_alpha M hγ j
        exact mul_le_mul_of_nonneg_right hw (hT0 j ω))
      (by simpa [mul_assoc] using hmajor)
  have hbaseTermInt (j : ℕ) : Integrable (baseTerm j) μ := by
    simpa [baseTerm] using (hTint j).const_mul (W j)
  have hbaseTermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ baseTerm j ω := by
    exact mul_nonneg (local_weight_nonneg'' M j) (hT0 j ω)
  have hbaseTermCap (j : ℕ) :
      (∫ ω, baseTerm j ω ∂μ) ≤
        W j * inSourceMeanActual M m (5 + j) t := by
    change (∫ ω, W j * T j ω ∂μ) ≤
      W j * inSourceMeanActual M m (5 + j) t
    rw [integral_const_mul, hmean]
  have hbaseIntegral := local_nonnegative_series_integral_ae μ
    baseTerm (fun j => W j * inSourceMeanActual M m (5 + j) t)
    hbaseTermInt hbaseTermNonneg hbaseAe hsource.1 hbaseTermCap
  have hbaseInt : Integrable baseSeries μ := by
    simpa [baseSeries] using hbaseIntegral.1
  have hbaseBound :
      (∫ ω, baseSeries ω ∂μ) ≤
        mixedXiPreCap M + t * mixedBridgeLocalSlope M h m := by
    calc
      _ ≤ ∑' j : ℕ, W j * inSourceMeanActual M m (5 + j) t := by
        simpa [baseSeries, baseTerm] using hbaseIntegral.2
      _ ≤ _ := hsource.2

  have hbank (j : ℕ) := local_bank_depth_block
    M h hM hγ N hpast m hm t ht j
  have hR0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ R j ω := by
    change 0 ≤ positiveSplitRemainder _ _ _
    exact (positive_split _ _ _).1
  have hRmeas (j : ℕ) : AEStronglyMeasurable (R j) μ :=
    (hbank j).remainder_measurable.aestronglyMeasurable
  have hR128 (j : ℕ) : eLpNorm (R j) 128 μ ≤ ENNReal.ofReal (ε j) := by
    change eLpNorm
      (inverseBankDepthBlockRemainder .localInverse
        (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) j) 128 μ ≤ _
    exact (hbank j).remainder_L128
  have hε0 (j : ℕ) : 0 ≤ ε j := by
    unfold ε inverseBankDepthReserve inverseBankReserve bankDepthFrame
    positivity
  have hRdiscount (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      α ^ j * R j ω ≤ B ω := by
    simpa [R, B, α] using
      mixed_old_local_depth_remainder_discount_le_global M m t ht j ω
  have htraceAe := mixed_bridge_obscell_trace_weighted_summable_ae
    M h hM hγ N hpast m hm t ht U hU
  have hrareAe := local_rare_series_summable_ae μ α B R T
    hα0 hα1 hR0 hT0 hRdiscount htraceAe
  have hrareTermInt (j : ℕ) : Integrable (rareTerm j) μ := by
    have hh := local_remainder_trace_integrable (R j) (T j) (ε j) (C j)
      (hε0 j) (local_profile_nonneg M j)
      (hR0 j) (hT0 j) (hRmeas j) (hTmeas j) (hR128 j) (hprofile j)
    have heq : rareTerm j = fun ω => w j * (R j ω * T j ω) := by
      funext ω
      dsimp [rareTerm]
      ring
    rw [heq]
    exact hh.1.const_mul (w j)
  have hrareTermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ rareTerm j ω := by
    have hw0 : 0 ≤ w j := by
      dsimp [w]
      exact mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα0 hα1))
        (pow_nonneg hα0 _)
    have hwr0 : 0 ≤ w j * R j ω := mul_nonneg hw0 (hR0 j ω)
    simpa [rareTerm] using mul_nonneg hwr0 (hT0 j ω)
  have hrareCap (j : ℕ) :
      (∫ ω, rareTerm j ω ∂μ) ≤ w j * (ε j * C j) := by
    have hh := local_remainder_trace_integrable (R j) (T j) (ε j) (C j)
      (hε0 j) (local_profile_nonneg M j)
      (hR0 j) (hT0 j) (hRmeas j) (hTmeas j) (hR128 j) (hprofile j)
    have heq : rareTerm j = fun ω => w j * (R j ω * T j ω) := by
      funext ω
      dsimp [rareTerm]
      ring
    rw [heq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hh.2
      (by
        dsimp [w]
        exact mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα0 hα1))
          (pow_nonneg hα0 _))
  have hrareCoeffSummable : Summable (fun j : ℕ => w j * (ε j * C j)) := by
    have hbase := old_signed_depth_rare_summable M hγ
    have hscaled := hbase.mul_left (1 - α ^ 2)
    apply hscaled.congr
    intro j
    simp only [w, ε, C, α, rawWeakTraceProfileEnvelope, pow_mul]
    ring
  have hrareCoeffBound :
      (∑' j : ℕ, w j * (ε j * C j)) ≤
        (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    let S : ℝ := ∑' j : ℕ,
      α ^ (2 * j) * ε j * C j
    have hS0 : 0 ≤ S := by
      apply tsum_nonneg
      intro j
      exact mul_nonneg (mul_nonneg (pow_nonneg hα0 _) (hε0 j))
        (local_profile_nonneg M j)
    have hbudget := old_signed_directional_rare_delta M hγ
    have hraw : 13 * ((1 - α ^ 2) * S) ≤
        (1 / 10 ^ 12 : ℝ) * theta M := by
      simpa [S, C, ε, α, rawWeakTraceProfileEnvelope,
        pow_mul, mul_assoc, mul_left_comm, mul_comm] using hbudget
    have hsmall : (1 - α ^ 2) * S ≤
        (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
      have hscaled := mul_le_mul_of_nonneg_left hraw
        (by norm_num : (0 : ℝ) ≤ 1 / 13)
      calc
        _ = (1 / 13 : ℝ) * (13 * ((1 - α ^ 2) * S)) := by ring
        _ ≤ (1 / 13 : ℝ) * ((1 / 10 ^ 12 : ℝ) * theta M) := hscaled
        _ = (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by ring
    have hident : (∑' j : ℕ, w j * (ε j * C j)) = (1 - α ^ 2) * S := by
      calc
        _ = ∑' j : ℕ, (1 - α ^ 2) *
            (α ^ (2 * j) * ε j * C j) := by
          apply tsum_congr
          intro j
          dsimp [w]
          ring
        _ = _ := by rw [tsum_mul_left]
    rw [hident]
    exact hsmall
  have hrareIntegral := local_nonnegative_series_integral_ae μ
    rareTerm (fun j => w j * (ε j * C j)) hrareTermInt
    hrareTermNonneg hrareAe hrareCoeffSummable hrareCap
  have hrareInt : Integrable rareSeries μ := by
    simpa [rareSeries] using hrareIntegral.1
  have hrareBound :
      (∫ ω, rareSeries ω ∂μ) ≤
        (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    calc
      _ ≤ ∑' j : ℕ, w j * (ε j * C j) := by
        simpa [rareSeries, rareTerm] using hrareIntegral.2
      _ ≤ _ := hrareCoeffBound

  have hdecomp : ∀ᵐ ω ∂μ,
      mixedOldTheta M m U t ω = baseSeries ω + rareSeries ω := by
    filter_upwards [hbaseAe, hrareAe] with ω hbaseω hrareω
    have hterm (j : ℕ) :
        mixedOldThetaTerm M m U t j ω = baseTerm j ω + rareTerm j ω := by
      dsimp [mixedOldThetaTerm, mixedDepthTraceAverage,
        baseTerm, rareTerm, W, w, T, R, α]
      rw [mixed_old_depth_coefficient_formula]
      simp [mixedBridgeLocalWeight, mixedBridgeOldInverseBaseline]
      ring
    calc
      _ = ∑' j : ℕ, mixedOldThetaTerm M m U t j ω := by
        simp [mixedOldTheta]
      _ = ∑' j : ℕ, (baseTerm j ω + rareTerm j ω) := by
        apply tsum_congr
        exact hterm
      _ = _ := hbaseω.tsum_add hrareω
  have hsumInt : Integrable (fun ω => baseSeries ω + rareSeries ω) μ :=
    hbaseInt.add hrareInt
  have hthetaReverse : (fun ω => baseSeries ω + rareSeries ω) =ᵐ[μ]
      (fun ω => mixedOldTheta M m U t ω) := by
    filter_upwards [hdecomp] with ω hω
    exact hω.symm
  have hthetaInt : Integrable (fun ω => mixedOldTheta M m U t ω) μ :=
    hsumInt.congr hthetaReverse
  have hthetaIntegral :
      (∫ ω, mixedOldTheta M m U t ω ∂μ) =
        (∫ ω, baseSeries ω ∂μ) + (∫ ω, rareSeries ω ∂μ) := by
    rw [integral_congr_ae hdecomp, integral_add hbaseInt hrareInt]
  have hxiBound :
      mixedXiPreCap M + t * mixedBridgeLocalSlope M h m +
          (1 / (13 * 10 ^ 12 : ℝ)) * theta M ≤ mixedBridgeLocalXi5 M h m t := by
    unfold mixedBridgeLocalXi5
    exact le_of_eq (by ac_rfl)
  have hfinal :
      (∫ ω, mixedOldTheta M m U t ω ∂μ) ≤
        mixedBridgeLocalXi5 M h m t := by
    rw [hthetaIntegral]
    linarith [hbaseBound, hrareBound]
  refine ⟨hthetaInt, ?_⟩
  exact hfinal


end
end ASDExplicitGamma.Inverse
