module

public import ASDExplicitGamma.Inverse.ParentGapHolder
public import ASDExplicitGamma.Inverse.ParentGapObserver
public import ASDExplicitGamma.Inverse.BridgeTraceSummability
public import ASDExplicitGamma.Inverse.RawTraceSpatialAverage
public import ASDExplicitGamma.Scalar.FlatSourceQ3ActualBank
public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral
public import ASDExplicitGamma.Native.OldSignedDirectionalRareReserve
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit

/-! The local depth-bank remainder is paid against the actual transported
parent trace history, with the correlated global inverse history retained. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open MeasureTheory Filter Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Response
open ASDExplicitGamma.Scalar ASDExplicitGamma.Variational ASDExplicitGamma.Triadic
open scoped ENNReal

noncomputable section

private theorem parent_gap_nonnegative_series_integral_ae
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (f : I → Ω → ℝ) (C : I → ℝ)
    (hf : ∀ j, Integrable (f j) μ) (hn : ∀ j ω, 0 ≤ f j ω)
    (hs : ∀ᵐ ω ∂μ, Summable (fun j => f j ω)) (hC : Summable C)
    (hb : ∀ j, (∫ ω, f j ω ∂μ) ≤ C j) :
    Integrable (fun ω => ∑' j, f j ω) μ ∧
      (∫ ω, ∑' j, f j ω ∂μ) ≤ ∑' j, C j := by
  classical
  have hI : Summable (fun j => ∫ ω, f j ω ∂μ) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (hn j)) hb hC
  have hm : AEStronglyMeasurable (fun ω => ∑' j, f j ω) μ := by
    apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun s : Finset I => s.aestronglyMeasurable_fun_sum (fun j _ => (hf j).1))
    filter_upwards [hs] with ω hω
    exact hω.hasSum
  have he : (∫⁻ ω, ENNReal.ofReal (∑' j, f j ω) ∂μ) =
      ENNReal.ofReal (∑' j, ∫ ω, f j ω ∂μ) := by
    calc
      _ = ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hs] with ω hω
        exact ENNReal.ofReal_tsum_of_nonneg (fun j => hn j ω) hω
      _ = ∑' j, ∫⁻ ω, ENNReal.ofReal (f j ω) ∂μ := by
        rw [lintegral_tsum (fun j => (hf j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
      _ = ∑' j, ENNReal.ofReal (∫ ω, f j ω ∂μ) := by
        apply tsum_congr
        intro j
        exact (ofReal_integral_eq_lintegral_ofReal (hf j)
          (Filter.Eventually.of_forall (hn j))).symm
      _ = ENNReal.ofReal (∑' j, ∫ ω, f j ω ∂μ) := by
        symm
        exact ENNReal.ofReal_tsum_of_nonneg
          (fun j => integral_nonneg (hn j)) hI
  have hi : Integrable (fun ω => ∑' j, f j ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm
      (Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun j => hn j ω)))).mp
      (by rw [he]; exact ENNReal.ofReal_ne_top)
  have hnorm : Summable (fun j => ∫ ω, ‖f j ω‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] using hI
  refine ⟨hi, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hf hnorm]
  exact hI.tsum_le_tsum hb hC

private theorem parent_gap_global_local_rare_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B R T : Ω → ℝ) (β ε C : ℝ) (k : ℕ) (hk : k ≤ 3)
    (hβ : 0 ≤ β) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hB0 : ∀ ω, 0 ≤ B ω) (hR0 : ∀ ω, 0 ≤ R ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (hBmeas : AEStronglyMeasurable B μ) (hRmeas : AEStronglyMeasurable R μ)
    (hTmeas : AEStronglyMeasurable T μ)
    (hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => B ω ^ k * R ω * T ω) μ ∧
      (∫ ω, B ω ^ k * R ω * T ω ∂μ) ≤ β ^ k * ε * C := by
  have hHolder := parent_gap_global_local_rare_term B R T β ε C k hk
    hB0 hR0 hT0 hBmeas hRmeas hTmeas hB128 hR128 hT2
  have hnonneg (ω : Ω) : 0 ≤ B ω ^ k * R ω * T ω :=
    mul_nonneg (mul_nonneg (pow_nonneg (hB0 ω) k) (hR0 ω)) (hT0 ω)
  have hreal (ω : Ω) : ENNReal.ofReal (B ω ^ k * R ω * T ω) =
      ENNReal.ofReal (B ω) ^ k * ENNReal.ofReal (R ω) * ENNReal.ofReal (T ω) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (hB0 ω) k) (hR0 ω)),
      ENNReal.ofReal_mul (pow_nonneg (hB0 ω) k), ENNReal.ofReal_pow (hB0 ω)]
  have hbound : ∫⁻ ω, ENNReal.ofReal (B ω ^ k * R ω * T ω) ∂μ ≤
      ENNReal.ofReal (β ^ k * ε * C) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (B ω) ^ k * ENNReal.ofReal (R ω) *
            ENNReal.ofReal (T ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with ω
        exact hreal ω
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal β ^ k * ENNReal.ofReal ε) := hHolder
      _ = ENNReal.ofReal (β ^ k * ε * C) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hβ k) hε),
          ENNReal.ofReal_mul (pow_nonneg hβ k), ENNReal.ofReal_pow hβ]
        ring
  have hmeas : AEStronglyMeasurable (fun ω => B ω ^ k * R ω * T ω) μ :=
    (hBmeas.pow k).mul hRmeas |>.mul hTmeas
  have hi : Integrable (fun ω => B ω ^ k * R ω * T ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall hnonneg)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (pow_nonneg hβ k) hε) hC)).mp hbound

private theorem parent_gap_local_depth_remainder_nonneg
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω := by
  change 0 ≤ positiveSplitRemainder _ _ _
  exact (positive_split _ _ _).1

private theorem parent_gap_local_depth_bankmax_eq_response
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    (bankFiniteRootResponseMax (descendantsAtDepth (originCube 2 m) j) M m (m + 1)
      (bankPartialInsertionWeights m 1 t) ω).toReal =
      lemmaVInverseDepthMax (originCube 2 m)
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mixedBridgeResponseCoefficient m t ω)) j := by
  let Q := originCube 2 m
  have hmax : bankFiniteRootResponseMax (descendantsAtDepth Q j) M m (m + 1)
      (bankPartialInsertionWeights m 1 t) ω =
      ENNReal.ofReal (lemmaVInverseDepthMax Q (oldSignedPartialFrameField M m 1 t ω) j) := by
    exact old_signed_source_depth_block_max_eq M m 0 Q
      (by simpa [Q, Homogenization.descendantsAtDepth_zero]) t ⟨ht.1, ht.2⟩ ω j
  have hframe : lemmaVInverseDepthMax Q (oldSignedPartialFrameField M m 1 t ω) j =
      lemmaVInverseDepthMax Q
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mixedBridgeResponseCoefficient m t ω)) j := by
    have hold := old_signed_partial_inverse_depth M m 1 t ⟨ht.1, ht.2⟩ ω j
    simp only [Nat.cast_one, add_sub_cancel_right] at hold
    rw [hold, mixed_bridge_frame_inverse_depth_eq_sigma_actual M m t ω ht j]
  rw [hmax, ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg Q _ j), hframe]

private theorem parent_gap_local_depth_remainder_le_bankmax
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω ≤
      (bankFiniteRootResponseMax (descendantsAtDepth (originCube 2 m) j) M m (m + 1)
        (bankPartialInsertionWeights m 1 t) ω).toReal := by
  let Q := originCube 2 m
  have hmax : bankFiniteRootResponseMax (descendantsAtDepth Q j) M m (m + 1)
      (bankPartialInsertionWeights m 1 t) ω =
      ENNReal.ofReal (lemmaVInverseDepthMax Q (oldSignedPartialFrameField M m 1 t ω) j) := by
    exact old_signed_source_depth_block_max_eq M m 0 Q
      (by simpa [Q, Homogenization.descendantsAtDepth_zero]) t ⟨ht.1, ht.2⟩ ω j
  have hY : (bankFiniteRootResponseMax (descendantsAtDepth Q j) M m (m + 1)
      (bankPartialInsertionWeights m 1 t) ω).toReal =
      lemmaVInverseDepthMax Q (oldSignedPartialFrameField M m 1 t ω) j := by
    rw [hmax, ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg Q _ j)]
  have hdepthNonneg := inverse_bank_depth_nonneg .localInverse M j
  have hA : 0 ≤ inverseBankDepthA .localInverse M j := hdepthNonneg.1
  have hδ : 0 ≤ inverseBankDepthSlack M j := hdepthNonneg.2.2.le
  have hD0 : 0 ≤ lemmaVInverseDepthMax Q (oldSignedPartialFrameField M m 1 t ω) j :=
    lemmaVInverseDepthMax_nonneg Q _ j
  change positiveSplitRemainder
    (bankFiniteRootResponseMax (descendantsAtDepth Q j) M m (m + 1)
      (bankPartialInsertionWeights m 1 t) ω).toReal _ _ ≤ _
  calc
    _ = positiveSplitRemainder
        (lemmaVInverseDepthMax Q (oldSignedPartialFrameField M m 1 t ω) j)
        (inverseBankDepthA .localInverse M j) (inverseBankDepthSlack M j) := by rw [hY]
    _ ≤ lemmaVInverseDepthMax Q (oldSignedPartialFrameField M m 1 t ω) j := by
      unfold positiveSplitRemainder
      exact max_le_iff.mpr ⟨hD0, by linarith [hA, hδ]⟩
    _ = (bankFiniteRootResponseMax (descendantsAtDepth Q j) M m (m + 1)
        (bankPartialInsertionWeights m 1 t) ω).toReal := hY.symm

private theorem parent_gap_local_depth_remainder_discount_le_bstar
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    Scalar.inverseHistoryDiscount ^ j *
      oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω ≤
    mixedBridgeBstar M m t ω := by
  let Q := originCube 2 m
  let α := Scalar.inverseHistoryDiscount
  let B : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hdiscount := mixed_bridge_parent_depth_discount_le_bstar M m t ω ht j
  have hpos := parent_gap_local_depth_remainder_le_bankmax M m t ht j ω
  have hY := parent_gap_local_depth_bankmax_eq_response M m t ht j ω
  calc
    _ ≤ α ^ j * (bankFiniteRootResponseMax (descendantsAtDepth Q j) M m (m + 1)
        (bankPartialInsertionWeights m 1 t) ω).toReal :=
      mul_le_mul_of_nonneg_left hpos (pow_nonneg hα0 j)
    _ = α ^ j * lemmaVInverseDepthMax Q
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mixedBridgeResponseCoefficient m t ω)) j := by rw [hY]
    _ ≤ B ω := hdiscount

private theorem parent_gap_weighted_rare_series_summable_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (α : ℝ)
    (B : Ω → ℝ) (R T : ℕ → Ω → ℝ) (k : ℕ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hB0 : ∀ ω, 0 ≤ B ω) (hR0 : ∀ j ω, 0 ≤ R j ω)
    (hT0 : ∀ j ω, 0 ≤ T j ω)
    (hRbound : ∀ j ω, α ^ j * R j ω ≤ B ω)
    (htrace : ∀ᵐ ω ∂μ, Summable (fun j => α ^ j * T j ω)) :
    ∀ᵐ ω ∂μ, Summable (fun j =>
      ((1 - α ^ 2) * α ^ (2 * j)) * B ω ^ k * R j ω * T j ω) := by
  filter_upwards [htrace] with ω htrace
  have hlead : Summable (fun j : ℕ =>
      ((1 - α ^ 2) * B ω ^ (k + 1)) * (α ^ j * T j ω)) :=
    htrace.mul_left ((1 - α ^ 2) * B ω ^ (k + 1))
  have hineq (j : ℕ) :
      ((1 - α ^ 2) * α ^ (2 * j)) * B ω ^ k * R j ω * T j ω ≤
        ((1 - α ^ 2) * B ω ^ (k + 1)) * (α ^ j * T j ω) := by
    have hBpower : B ω ^ k * (α ^ j * R j ω) ≤ B ω ^ (k + 1) := by
      calc
        _ ≤ B ω ^ k * B ω :=
          mul_le_mul_of_nonneg_left (hRbound j ω) (pow_nonneg (hB0 ω) k)
        _ = B ω ^ (k + 1) := by rw [pow_succ]
    have hαpow : 0 ≤ α ^ j := pow_nonneg hα0 j
    have hTα : 0 ≤ α ^ j * T j ω := mul_nonneg hαpow (hT0 j ω)
    calc
      _ = (1 - α ^ 2) * (B ω ^ k * (α ^ j * R j ω)) * (α ^ j * T j ω) := by ring
      _ ≤ (1 - α ^ 2) * B ω ^ (k + 1) * (α ^ j * T j ω) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBpower
            (sub_nonneg.mpr (pow_le_one₀ hα0 hα1))) hTα
      _ = _ := by ring
  have hW0 (j : ℕ) : 0 ≤ (1 - α ^ 2) * α ^ (2 * j) :=
    mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα0 hα1)) (pow_nonneg hα0 _)
  have hmajor : Summable (fun j : ℕ =>
      ((1 - α ^ 2) * α ^ (2 * j)) * B ω ^ k * (R j ω * T j ω)) := by
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (mul_nonneg (hW0 j) (pow_nonneg (hB0 ω) k))
        (mul_nonneg (hR0 j ω) (hT0 j ω)))
      (fun j => by simpa only [mul_assoc] using hineq j) hlead
  simpa only [mul_assoc] using hmajor

private theorem parent_gap_local_depth_rare_series_ae_summable_core
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        (mixedBridgeBstar M m t ω) ^ k *
        oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω *
        mixedBridgeTbar M m t ω j) := by
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let Q := originCube 2 m
  let B : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  let R : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    oldSignedSourceDepthRemainder M m t Q j ω
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    mixedBridgeTbar M m t ω j
  have hα := Scalar.inverse_history_discount_range
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := by
    intro j
    apply hpast
    omega
  have htrace := mixed_bridge_raw_trace_weighted_summable_ae
    M h hM hγ m t ht hstate
  have hs := parent_gap_weighted_rare_series_summable_ae μ α B R T k
    hα.1.le hα.2.le
    (fun ω => mixed_bridge_bstar_nonneg M m t ω)
    (fun j ω => parent_gap_local_depth_remainder_nonneg M m t j ω)
    (fun j ω => raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j)
    (fun j ω => parent_gap_local_depth_remainder_discount_le_bstar M m t ht j ω)
    htrace
  simpa only [B, R, T, α, Q] using hs

/-- The complete local depth-remainder payment for the parent trace history.
It keeps the actual `B*`, local bank remainder, raw child trace, and squared
history weights in one correlated expectation. -/
theorem parent_gap_local_depth_rare_series_sharp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : k ≤ 3) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable (fun ω => ∑' j : ℕ,
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        (mixedBridgeBstar M m t ω) ^ k *
        oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω *
        mixedBridgeTbar M m t ω j) μ ∧
      (∫ ω, ∑' j : ℕ,
        ((1 - Scalar.inverseHistoryDiscount ^ 2) *
          Scalar.inverseHistoryDiscount ^ (2 * j)) *
          (mixedBridgeBstar M m t ω) ^ k *
          oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω *
          mixedBridgeTbar M m t ω j ∂μ) ≤
        ((14103 / 10000 : ℝ) ^ k) * (1 / (13 * 10 ^ 12) : ℝ) * theta M := by
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let Q := originCube 2 m
  let B : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  let εj : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    oldSignedSourceDepthRemainder M m t Q j ω
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    mixedBridgeTbar M m t ω j
  let w : ℕ → ℝ := fun j => (1 - α ^ 2) * α ^ (2 * j)
  let C : ℕ → ℝ := fun j =>
    theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
      (3 : ℝ) ^ (6 * gammaZero * j)
  let eps : ℕ → ℝ := fun j => inverseBankDepthReserve .localInverse M j
  let β : ℝ := 14103 / 10000

  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hθ : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hinvTraceQ : 0 ≤ invTraceM := by
    rw [invTrace_coefficient.1]
    positivity
  have hinvTrace : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hinvTraceQ
  have hβ : 0 ≤ β := by norm_num [β]
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := by
    intro j
    apply hpast
    omega
  have hglobal := mixed_bridge_global_bank_split M h hM hγ m t ht hstate
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω :=
    mixed_bridge_bstar_nonneg M m t ω
  have hB128ENN : eLpNorm (fun ω => ENNReal.ofReal (B ω)) 128 μ ≤
      ENNReal.ofReal β := by
    simpa [B, β, inverseBankCap] using hglobal.2.1
  have hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β := by
    rw [← eLpNorm_ofReal B (Filter.Eventually.of_forall hB0)]
    exact hB128ENN
  have hBmeas : AEStronglyMeasurable B μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top
      (hB128.trans_lt ENNReal.ofReal_lt_top).ne
  have hMold : ∀ l < m, nativeInductionState M h l := by
    intro l hl
    exact hpast l (hl.trans hm)
  have hstateZero : ∀ q : ℕ,
      nativeInductionState M h (m - (0 : ℤ) - (q : ℤ)) := by
    intro q
    simpa using hstate q
  have hTprofile := raw_trace_transport_profile_and_reserves_source
    M h hM hγ m 0 (by norm_num) t ht hstateZero
  have hT0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ T j ω := by
    exact raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j
  have hC0 (j : ℕ) : 0 ≤ C j := by
    dsimp [C]
    positivity
  have hT2 (j : ℕ) : eLpNorm (T j) 2 μ ≤ ENNReal.ofReal (C j) := by
    have hh := hTprofile.1 j
    simp only [Nat.cast_zero, Int.sub_zero] at hh
    have hcast : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    simpa only [T, mixedBridgeTbar, rawWeakTraceSequence, hcast, C, μ] using hh
  have hTmem (j : ℕ) : MemLp (T j) 2 μ :=
    memLp_iff.mpr ((hT2 j).trans_lt ENNReal.ofReal_lt_top)
  have hTmeas (j : ℕ) : AEStronglyMeasurable (T j) μ := (hTmem j).aestronglyMeasurable

  have hdepth (j : ℕ) : InverseBankDepthBlockConclusion M .localInverse
      (descendantsAtDepth Q j) m (m + 1)
      (bankPartialInsertionWeights m 1 t) j := by
    exact old_signed_source_depth_block_bank M h hM hγ m t ⟨ht.1, ht.2⟩
      hMold 0 (by norm_num) Q (by change m = m - (0 : ℤ); omega) j
  have hR0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ εj j ω :=
    parent_gap_local_depth_remainder_nonneg M m t j ω
  have hRmeas (j : ℕ) : AEStronglyMeasurable (εj j) μ :=
    (hdepth j).remainder_measurable.aestronglyMeasurable
  have hR128 (j : ℕ) : eLpNorm (εj j) 128 μ ≤ ENNReal.ofReal (eps j) := by
    change eLpNorm
      (inverseBankDepthBlockRemainder .localInverse (descendantsAtDepth Q j) M m
        (m + (1 : ℕ)) (bankPartialInsertionWeights m 1 t) j) 128 μ ≤
      ENNReal.ofReal (inverseBankDepthReserve .localInverse M j)
    exact (hdepth j).remainder_L128
  have hε0 (j : ℕ) : 0 ≤ eps j := by
    unfold eps inverseBankDepthReserve inverseBankReserve bankDepthFrame
    positivity
  have hw0 (j : ℕ) : 0 ≤ w j := by
    unfold w
    exact mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα0 hα.2.le))
      (pow_nonneg hα0 _)

  have hperDepth (j : ℕ) :
      Integrable (fun ω => B ω ^ k * εj j ω * T j ω) μ ∧
        (∫ ω, B ω ^ k * εj j ω * T j ω ∂μ) ≤ β ^ k * eps j * C j := by
    exact parent_gap_global_local_rare_integrable B (εj j) (T j)
      β (eps j) (C j) k hk hβ (hε0 j) (hC0 j) hB0 (hR0 j) (hT0 j)
      hBmeas (hRmeas j) (hTmeas j) hB128 (hR128 j) (hT2 j)

  have hcoeffSummable : Summable (fun j : ℕ => w j * (β ^ k * eps j * C j)) := by
    have hbase := old_signed_depth_rare_summable M hγ
    have hscale : Summable (fun j : ℕ =>
        ((1 - α ^ 2) * β ^ k) *
          (α ^ (2 * j) * inverseBankDepthReserve .localInverse M j *
            (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
              (3 : ℝ) ^ (6 * gammaZero * j)))) :=
      hbase.mul_left ((1 - α ^ 2) * β ^ k)
    apply hscale.congr
    intro j
    simp only [w, C, eps, pow_mul]
    ring

  have hbudget := old_signed_directional_rare_delta M hγ
  have hcoeffBound : (∑' j : ℕ, w j * (β ^ k * eps j * C j)) ≤
      β ^ k * (1 / (13 * 10 ^ 12) : ℝ) * theta M := by
    have hident : (∑' j : ℕ, w j * (β ^ k * eps j * C j)) =
        ((1 - α ^ 2) * β ^ k) *
          (∑' j : ℕ, α ^ (2 * j) * eps j * C j) := by
      calc
        _ = ∑' j : ℕ, ((1 - α ^ 2) * β ^ k) *
              (α ^ (2 * j) * eps j * C j) := by
          apply tsum_congr
          intro j
          simp only [w]
          ring
        _ = _ := tsum_mul_left
    rw [hident]
    have hsum0 : 0 ≤ ∑' j : ℕ, α ^ (2 * j) * eps j * C j :=
      tsum_nonneg (fun j => mul_nonneg (mul_nonneg (pow_nonneg hα0 _) (hε0 j)) (hC0 j))
    have hraw : 13 * ((1 - α ^ 2) *
        (∑' j : ℕ, α ^ (2 * j) * eps j * C j)) ≤
        (1 / 10 ^ 12 : ℝ) * theta M := by
      simpa [eps, C, pow_mul, mul_assoc, mul_left_comm, mul_comm] using hbudget
    have hbase : (1 - α ^ 2) *
        (∑' j : ℕ, α ^ (2 * j) * eps j * C j) ≤
        (1 / (13 * 10 ^ 12) : ℝ) * theta M := by
      have hscaled := mul_le_mul_of_nonneg_left hraw
        (by norm_num : (0 : ℝ) ≤ 1 / 13)
      calc
        _ = (1 / 13 : ℝ) *
            (13 * ((1 - α ^ 2) *
              (∑' j : ℕ, α ^ (2 * j) * eps j * C j))) := by ring
        _ ≤ (1 / 13 : ℝ) * ((1 / 10 ^ 12 : ℝ) * theta M) := hscaled
        _ = (1 / (13 * 10 ^ 12) : ℝ) * theta M := by ring
    calc
      _ = β ^ k * ((1 - α ^ 2) * (∑' j : ℕ, α ^ (2 * j) * eps j * C j)) := by ring
      _ ≤ β ^ k * ((1 / (13 * 10 ^ 12) : ℝ) * theta M) :=
        mul_le_mul_of_nonneg_left hbase (pow_nonneg hβ k)
      _ = β ^ k * (1 / (13 * 10 ^ 12) : ℝ) * theta M := by ring

  have hpointwiseSummable := parent_gap_local_depth_rare_series_ae_summable_core
    M h hM hγ N hpast m hm t ht k
  have hpointwiseSummable : ∀ᵐ ω ∂μ,
      Summable (fun j : ℕ => w j * B ω ^ k * εj j ω * T j ω) := by
    simpa only [B, εj, T, w, α, Q] using hpointwiseSummable

  have htermInt (j : ℕ) : Integrable
      (fun ω => w j * B ω ^ k * εj j ω * T j ω) μ := by
    have hbase := (hperDepth j).1.const_mul (w j)
    convert hbase using 1 <;> ext ω <;> ring
  have htermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ w j * B ω ^ k * εj j ω * T j ω := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw0 j) (pow_nonneg (hB0 ω) k))
      (hR0 j ω)) (hT0 j ω)
  have hcap (j : ℕ) :
      (∫ ω, w j * B ω ^ k * εj j ω * T j ω ∂μ) ≤
        w j * (β ^ k * eps j * C j) := by
    rw [show (fun ω => w j * B ω ^ k * εj j ω * T j ω) =
      fun ω => w j * (B ω ^ k * εj j ω * T j ω) by funext ω; ring,
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hperDepth j).2 (hw0 j)
  have hseries := parent_gap_nonnegative_series_integral_ae μ
    (fun j ω => w j * B ω ^ k * εj j ω * T j ω)
    (fun j => w j * (β ^ k * eps j * C j))
    htermInt htermNonneg hpointwiseSummable hcoeffSummable hcap
  refine ⟨?_, ?_⟩
  · simpa only [B, εj, T, w, α, Q] using hseries.1
  · calc
      _ ≤ ∑' j : ℕ, w j * (β ^ k * eps j * C j) := by
        simpa only [B, εj, T, w, α, Q] using hseries.2
      _ ≤ β ^ k * (1 / (13 * 10 ^ 12) : ℝ) * theta M := hcoeffBound

/-- The sharp local rare-payment estimate together with the a.e. summability
needed to compare its real tsum with pointwise sums in downstream assemblies. -/
theorem parent_gap_local_depth_rare_series_summable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : k ≤ 3) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable (fun ω => ∑' j : ℕ,
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        (mixedBridgeBstar M m t ω) ^ k *
        oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω *
        mixedBridgeTbar M m t ω j) μ ∧
      (∫ ω, ∑' j : ℕ,
        ((1 - Scalar.inverseHistoryDiscount ^ 2) *
          Scalar.inverseHistoryDiscount ^ (2 * j)) *
          (mixedBridgeBstar M m t ω) ^ k *
          oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω *
          mixedBridgeTbar M m t ω j ∂μ) ≤
        ((14103 / 10000 : ℝ) ^ k) * (1 / (13 * 10 ^ 12) : ℝ) * theta M ∧
      (∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
        ((1 - Scalar.inverseHistoryDiscount ^ 2) *
          Scalar.inverseHistoryDiscount ^ (2 * j)) *
          (mixedBridgeBstar M m t ω) ^ k *
          oldSignedSourceDepthRemainder M m t (originCube 2 m) j ω *
          mixedBridgeTbar M m t ω j)) := by
  have hsharp := parent_gap_local_depth_rare_series_sharp
    M h hM hγ N hpast m hm t ht k hk
  have hsum := parent_gap_local_depth_rare_series_ae_summable_core
    M h hM hγ N hpast m hm t ht k
  dsimp only at hsharp hsum ⊢
  exact ⟨hsharp.1, hsharp.2, hsum⟩

end
end ASDExplicitGamma.Inverse
