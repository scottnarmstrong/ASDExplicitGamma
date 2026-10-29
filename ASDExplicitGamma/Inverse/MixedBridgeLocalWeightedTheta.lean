module

public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.ParentGapHolder
public import ASDExplicitGamma.Inverse.BridgeGlobalBank
public import ASDExplicitGamma.Native.OldSignedRarePowerPayment
public import ASDExplicitGamma.Native.OldSignedDirectionalRareReserve

/-! Correlated local OLD-Theta moments for the depth-five source cells. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Filter Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

private theorem nonnegative_series_integral_ae'
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

private theorem local_weight_le_alpha
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

private theorem local_weight_nonneg (M : ABKModel 2) (j : ℕ) :
    0 ≤ mixedBridgeLocalWeight M j := by
  unfold mixedBridgeLocalWeight mixedBridgeOldInverseBaseline
  have hα := Scalar.inverse_history_discount_range
  have hpref : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    nlinarith [hα.1, hα.2]
  exact mul_nonneg (mul_nonneg hpref
      (pow_nonneg hα.1.le _))
    (mul_nonneg (by norm_num : 0 ≤ (3683 / 2500 : ℝ))
      (Real.rpow_nonneg (by norm_num) _))

private theorem local_trace_nonneg
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ mixedDepthTraceAverage M m U t ω j := by
  simpa [mixedDepthTraceAverage] using
    raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j

private theorem profile_nonneg' (M : ABKModel 2) (j : ℕ) :
    0 ≤ rawWeakTraceProfileEnvelope M j := by
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by
    rw [invTrace_coefficient.1]
    positivity
  have hM : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
  unfold rawWeakTraceProfileEnvelope
  positivity

private theorem weighted_rare_series_summable_ae
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
    have hTα : 0 ≤ α ^ j * T j ω :=
      mul_nonneg (pow_nonneg hα0 j) (hT0 j ω)
    calc
      _ = (1 - α ^ 2) * (B ω ^ k * (α ^ j * R j ω)) *
          (α ^ j * T j ω) := by ring
      _ ≤ (1 - α ^ 2) * B ω ^ (k + 1) * (α ^ j * T j ω) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBpower
            (sub_nonneg.mpr (pow_le_one₀ hα0 hα1))) hTα
      _ = _ := by ring
  have hweight0 (j : ℕ) : 0 ≤ (1 - α ^ 2) * α ^ (2 * j) :=
    mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα0 hα1)) (pow_nonneg hα0 _)
  have hmajor : Summable (fun j : ℕ =>
      ((1 - α ^ 2) * α ^ (2 * j)) * B ω ^ k * (R j ω * T j ω)) := by
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (mul_nonneg (hweight0 j) (pow_nonneg (hB0 ω) k))
        (mul_nonneg (hR0 j ω) (hT0 j ω)))
      (fun j => by simpa only [mul_assoc] using hineq j) hlead
  simpa only [mul_assoc] using hmajor

private theorem correlated_B_power_R_trace_integrable
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
  have hholder := parent_gap_global_local_rare_term B R T β ε C k hk
    hB0 hR0 hT0 hBmeas hRmeas hTmeas hB128 hR128 hT2
  have hnonneg (ω : Ω) : 0 ≤ B ω ^ k * R ω * T ω :=
    mul_nonneg (mul_nonneg (pow_nonneg (hB0 ω) k) (hR0 ω)) (hT0 ω)
  have hreal (ω : Ω) :
      ENNReal.ofReal (B ω ^ k * R ω * T ω) =
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
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal β ^ k * ENNReal.ofReal ε) := hholder
      _ = ENNReal.ofReal (β ^ k * ε * C) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hβ k) hε),
          ENNReal.ofReal_mul (pow_nonneg hβ k), ENNReal.ofReal_pow hβ]
        ring
  have hmeas : AEStronglyMeasurable
      (fun ω => B ω ^ k * R ω * T ω) μ := (hBmeas.pow k).mul hRmeas |>.mul hTmeas
  have hi : Integrable (fun ω => B ω ^ k * R ω * T ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall hnonneg)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall hnonneg)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (pow_nonneg hβ k) hε) hC)).mp hbound

private theorem rare_tail_thirteen'
    (ε C : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000)
    (hC : 0 ≤ C) (k : ℕ) (hk : k ≤ 3) :
    rareExpansionTail (14103 / 10000 : ℝ) ε C k ≤ 13 * ε * C := by
  have hε2 : ε ^ 2 ≤ ε * (1 / 1000 : ℝ) := by
    have hdiff : 0 ≤ (1 / 1000 : ℝ) - ε := sub_nonneg.mpr hεsmall
    nlinarith [mul_nonneg hε hdiff]
  have hε3 : ε ^ 3 ≤ ε * (1 / 1000 : ℝ) ^ 2 := by
    calc
      ε ^ 3 = ε ^ 2 * ε := by ring
      _ ≤ (ε * (1 / 1000 : ℝ)) * ε :=
        mul_le_mul_of_nonneg_right hε2 hε
      _ = ε ^ 2 * (1 / 1000 : ℝ) := by ring
      _ ≤ (ε * (1 / 1000 : ℝ)) * (1 / 1000 : ℝ) :=
        mul_le_mul_of_nonneg_right hε2 (by norm_num)
      _ = ε * (1 / 1000 : ℝ) ^ 2 := by ring
  have hscalar : rareExpansionTail (14103 / 10000 : ℝ) ε 1 k ≤ 13 * ε := by
    interval_cases k <;>
      norm_num [rareExpansionTail, Finset.sum_Icc_succ_top, Nat.choose] <;>
      nlinarith [hε, hε2, hε3]
  rw [old_signed_rare_tail_linear (14103 / 10000 : ℝ) ε C k]
  exact mul_le_mul_of_nonneg_right hscalar hC

private theorem global_rare_budget
    (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => mixedBridgeLocalWeight M j *
      (13 * (1 / 10 ^ 24 : ℝ) * rawWeakTraceProfileEnvelope M j)) ∧
      (∑' j : ℕ, mixedBridgeLocalWeight M j *
        (13 * (1 / 10 ^ 24 : ℝ) * rawWeakTraceProfileEnvelope M j)) ≤
        (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
  let α := Scalar.inverseHistoryDiscount
  let b₀ : ℝ := 3683 / 2500
  let ε : ℝ := 1 / 10 ^ 24
  let q : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ) + 2 * M.gamma +
    6 * gammaZero + 1 / 64)
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hinvTraceQ : 0 ≤ invTraceM := by
    rw [invTrace_coefficient.1]
    positivity
  have hinvTrace : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hinvTraceQ
  have hC0 (j : ℕ) : 0 ≤ rawWeakTraceProfileEnvelope M j :=
    profile_nonneg' M j
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hratio : q ≤ 9 / 10 := by
    dsimp [q]
    exact old_signed_depth_rare_ratio M hγ
  have hgeom := native_source_quadratic_geometric_sum (9 / 10 : ℝ)
    (by norm_num) (by norm_num)
  have hdepth (j : ℕ) :
      α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) *
        (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) ≤ q ^ j := by
    have hpop : 1 ≤ (9 : ℝ) ^ ((j : ℝ) / 128) := by
      apply Real.one_le_rpow (by norm_num)
      positivity
    have hbase0 : 0 ≤ α ^ (2 * j) * bankDepthFrame M j :=
      mul_nonneg (pow_nonneg hα0 _) (bankDepthFrame_pos M j).le
    have hgamma0 : 0 ≤ (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    calc
      _ = (α ^ (2 * j) * bankDepthFrame M j) *
          (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) := by
        simp [bankDepthFrame]
      _ ≤ (α ^ (2 * j) * bankDepthFrame M j) *
          (9 : ℝ) ^ ((j : ℝ) / 128) *
          (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) := by
        have hh := mul_le_mul_of_nonneg_left hpop hbase0
        have hh' : α ^ (2 * j) * bankDepthFrame M j ≤
            (α ^ (2 * j) * bankDepthFrame M j) *
              (9 : ℝ) ^ ((j : ℝ) / 128) := by simpa using hh
        exact mul_le_mul_of_nonneg_right hh' hgamma0
      _ = q ^ j := by
        simpa [q, α] using old_signed_depth_rare_weight M j
  let c : ℝ := (1 - α ^ 2) * b₀ * (13 * ε) * theta M * (invTraceM : ℝ)
  have hc0 : 0 ≤ c := by
    dsimp [c, ε, b₀]
    have hpref : 0 ≤ 1 - α ^ 2 := by
      nlinarith [hα.1, hα.2, sq_nonneg α]
    positivity
  have hCbound (j : ℕ) :
      mixedBridgeLocalWeight M j *
        (13 * ε * rawWeakTraceProfileEnvelope M j) ≤
      c * (((j : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ j) := by
    have hweight : mixedBridgeLocalWeight M j =
        (1 - α ^ 2) * b₀ * α ^ (2 * j) *
          (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
      unfold mixedBridgeLocalWeight mixedBridgeOldInverseBaseline
      dsimp [α, b₀]
      ring
    have hdepth' := hdepth j
    have hpowle : q ^ j ≤ (9 / 10 : ℝ) ^ j :=
      pow_le_pow_left₀ hq0 hratio j
    rw [hweight]
    unfold rawWeakTraceProfileEnvelope
    calc
      _ = c * (((j : ℝ) + 1) ^ 2 *
          (α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) *
            (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)))) := by
        dsimp [c, ε]
        ring
      _ ≤ c * (((j : ℝ) + 1) ^ 2 * q ^ j) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdepth' (sq_nonneg _)) hc0
      _ ≤ c * (((j : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ j) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpowle (sq_nonneg _)) hc0
  have hbudgetNN (j : ℕ) :
      0 ≤ mixedBridgeLocalWeight M j *
        (13 * ε * rawWeakTraceProfileEnvelope M j) :=
    mul_nonneg (local_weight_nonneg M j)
      (mul_nonneg (by norm_num [ε]) (profile_nonneg' M j))
  have hbudgetDom : Summable (fun j : ℕ =>
      c * (((j : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ j)) := hgeom.1.mul_left c
  have hbudget : Summable (fun j : ℕ =>
      mixedBridgeLocalWeight M j *
        (13 * ε * rawWeakTraceProfileEnvelope M j)) :=
    Summable.of_nonneg_of_le hbudgetNN hCbound hbudgetDom
  have hsum := hbudget.tsum_le_tsum hCbound hbudgetDom
  have htraceCap : (invTraceM : ℝ) ≤ 10 ^ 6 := by
    exact_mod_cast invTrace_coefficient.2.1.le
  have hnum : (1 - α ^ 2) * b₀ * (13 * ε) * 1900 * 10 ^ 6 ≤
      1 / (13 * 10 ^ 12 : ℝ) := by
    have hpref : 0 ≤ 1 - α ^ 2 ∧ 1 - α ^ 2 ≤ 1 := by
      constructor <;> nlinarith [hα.1, hα.2, sq_nonneg α]
    have hcore0 : 0 ≤ b₀ * (13 * ε) * 1900 * 10 ^ 6 := by
      dsimp [b₀, ε]
      positivity
    calc
      _ ≤ 1 * (b₀ * (13 * ε) * 1900 * 10 ^ 6) := by
        calc
          _ = (1 - α ^ 2) * (b₀ * (13 * ε) * 1900 * 10 ^ 6) := by ring
          _ ≤ 1 * (b₀ * (13 * ε) * 1900 * 10 ^ 6) :=
            mul_le_mul_of_nonneg_right hpref.2 hcore0
      _ ≤ 1 / (13 * 10 ^ 12 : ℝ) := by
        norm_num [b₀, ε]
  have hcoeff : c * 1900 ≤ (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    dsimp [c]
    calc
      _ ≤ ((1 - α ^ 2) * b₀ * (13 * ε) * 1900 * 10 ^ 6) * theta M := by
        have hαsq : 0 ≤ 1 - α ^ 2 := by
          nlinarith [hα.1, hα.2, sq_nonneg α]
        have hfactor : 0 ≤ (1 - α ^ 2) * b₀ * (13 * ε) * 1900 * theta M :=
          mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg hαsq (by norm_num [b₀]))
                (by positivity))
              (by norm_num))
            htheta
        calc
          _ = ((1 - α ^ 2) * b₀ * (13 * ε) * 1900 * theta M) *
              (invTraceM : ℝ) := by ring
          _ ≤ ((1 - α ^ 2) * b₀ * (13 * ε) * 1900 * theta M) * 10 ^ 6 :=
            mul_le_mul_of_nonneg_left htraceCap hfactor
          _ = _ := by ring
      _ ≤ (1 / (13 * 10 ^ 12 : ℝ)) * theta M :=
        by
          have hnumTheta := mul_le_mul_of_nonneg_right hnum htheta
          nlinarith [hnumTheta]
  refine ⟨hbudget, ?_⟩
  calc
    _ ≤ c * 1900 := by
      rw [tsum_mul_left, hgeom.2] at hsum
      norm_num only [show (1 + (9 / 10 : ℝ)) /
        (1 - 9 / 10) ^ 3 = 1900 by norm_num] at hsum
      have hεrat :
          (13 / 1000000000000000000000000 : ℝ) =
            13 * (1 / 10 ^ 24 : ℝ) := by norm_num
      simpa only [hεrat] using hsum
    _ ≤ (1 / (13 * 10 ^ 12 : ℝ)) * theta M := hcoeff

private theorem local_union_depth_block
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

/-- Correlated depth-five local moment row with both bank remainders paid
separately. Its exact center and shifted source slope are left visible for the
source-envelope comparison in the main theorem. -/
theorem mixed_bridge_local_weighted_old_theta_xi5
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 m) 5)
    (k : Fin 4) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable (fun ω => mixedBridgeBstar M m t ω ^ k.val *
      mixedOldTheta M m U t ω) μ ∧
    (∫ ω, mixedBridgeBstar M m t ω ^ k.val *
      mixedOldTheta M m U t ω ∂μ) ≤
      (14103 / 10000 : ℝ) ^ k.val *
        (mixedXiPreCap M + (1 / 10 ^ 12 : ℝ) * theta M +
          t * mixedBridgeLocalSlope M h m) := by
  classical
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let β : ℝ := 14103 / 10000
  let b₀ : ℝ := 3683 / 2500
  let ε : ℝ := 1 / 10 ^ 24
  let w : ℕ → ℝ := fun j => (1 - α ^ 2) * α ^ (2 * j)
  let b : ℕ → ℝ := mixedBridgeOldInverseBaseline M
  let W : ℕ → ℝ := mixedBridgeLocalWeight M
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ :=
    fun j ω => mixedDepthTraceAverage M m U t ω j
  let C : ℕ → ℝ := fun j => rawWeakTraceProfileEnvelope M j
  let B : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  let Rglobal : Cutoff.CutoffSample 2 → ℝ := inverseBankPopulationRemainder
    .globalInverse (mixedBridgeObserverSourceRoots m) M m (m + 40)
    (bankPartialInsertionWeights m 1 t)
  let Rlocal : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    mixedOldLocalDepthRemainder M m t j ω
  let sourceTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => W j * T j ω
  let sourceSeries : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, sourceTerm j ω
  let baseTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    W j * B ω ^ k.val * T j ω
  let baseSeries : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, baseTerm j ω
  let globalRareTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    W j * rareExpansionTail β (Rglobal ω) (T j ω) k.val
  let globalRare : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, globalRareTerm j ω
  let localTerm : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    w j * B ω ^ k.val * Rlocal j ω * T j ω
  let localSeries : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j, localTerm j ω
  let epsLocal : ℕ → ℝ := fun j => inverseBankDepthReserve .localInverse M j

  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hα1 : α ≤ 1 := hα.2.le
  have hβ0 : 0 ≤ β := by norm_num [β]
  have hβ1 : 1 ≤ β := by norm_num [β]
  have hb₀ : 0 ≤ b₀ := by norm_num [b₀]
  have hε0 : 0 ≤ ε := by norm_num [ε]
  have hεsmall : ε ≤ 1 / 1000 := by norm_num [ε]
  have hθ : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω :=
    mixed_bridge_bstar_nonneg M m t ω
  have hT0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ T j ω := by
    simpa [T] using local_trace_nonneg M m U t ht j ω
  have hC0 (j : ℕ) : 0 ≤ C j := by simpa [C] using profile_nonneg' M j
  have hBstarWeight (j : ℕ) : W j = w j * b j := by
    dsimp [W, w, b, α, mixedBridgeLocalWeight,
      mixedBridgeOldInverseBaseline, Scalar.inverseHistoryDiscount]
  have hW0 (j : ℕ) : 0 ≤ W j := by
    exact local_weight_nonneg M j
  have hWle (j : ℕ) : W j ≤ b₀ * α ^ j := by
    simpa [W, b₀, α] using local_weight_le_alpha M hγ j

  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := by
    intro j
    apply hpast
    omega
  have hglobal := mixed_bridge_global_bank_split M h hM hγ m t ht hstate
  have hglobalBank := mixed_bridge_global_bank_inputs M h hM hγ m t ht hstate
  have hB128ENN : eLpNorm (fun ω => ENNReal.ofReal (B ω)) 128 μ ≤
      ENNReal.ofReal β := by
    simpa [B, β, inverseBankCap, μ] using hglobal.2.1
  have hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β := by
    rw [← eLpNorm_ofReal B (Filter.Eventually.of_forall hB0)]
    exact hB128ENN
  have hBmeas : AEStronglyMeasurable B μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top
      (hB128.trans_lt ENNReal.ofReal_lt_top).ne
  have hRglobal0 (ω : Cutoff.CutoffSample 2) : 0 ≤ Rglobal ω := by
    simpa [Rglobal] using hglobalBank.remainder_nonneg ω
  have hRglobalMeas : AEStronglyMeasurable Rglobal μ := by
    simpa [Rglobal, μ] using hglobalBank.remainder_measurable.aestronglyMeasurable
  have hRglobal128 : eLpNorm Rglobal 128 μ ≤ ENNReal.ofReal ε := by
    simpa [Rglobal, μ, ε, inverseBankReserve] using hglobal.2.2
  have hBsplit : ∀ᵐ ω ∂μ, B ω ≤ β + Rglobal ω := by
    filter_upwards [hglobal.1] with ω hω
    have hω' : ENNReal.ofReal (B ω) ≤
        ENNReal.ofReal β + ENNReal.ofReal (Rglobal ω) := by
      simpa [B, β, Rglobal, inverseBankCap] using hω
    rw [← ENNReal.ofReal_add hβ0 (hRglobal0 ω)] at hω'
    exact (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg hβ0 (hRglobal0 ω))).mp hω'

  have hprofile (j : ℕ) : eLpNorm (T j) 2 μ ≤ ENNReal.ofReal (C j) := by
    simpa [T, C, μ] using mixed_bridge_local_trace_profile
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
    simpa [T, μ] using
      (mixed_bridge_local_trace_mean M h hM hγ N hpast m hm t ht
        5 (by omega) U hU j).2

  have htraceAe := mixed_bridge_local_trace_weighted_summable_ae
    M h hM hγ N hpast m hm t ht U hU
  have hsourceAe : ∀ᵐ ω ∂μ, Summable (fun j => sourceTerm j ω) := by
    filter_upwards [htraceAe] with ω hω
    have hmajor := hω.mul_left b₀
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (hW0 j) (hT0 j ω))
      (fun j => mul_le_mul_of_nonneg_right (hWle j) (hT0 j ω))
      (by simpa [sourceTerm, T, α, b₀, mul_assoc] using hmajor)
  have hsourceInt (j : ℕ) : Integrable (sourceTerm j) μ := by
    simpa [sourceTerm] using (hTint j).const_mul (W j)
  have hsourceTermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ sourceTerm j ω := mul_nonneg (hW0 j) (hT0 j ω)
  have hsource := mixed_bridge_local_mean_transport
    M h hM hγ N hpast m hm t ht
  have hsourceCap (j : ℕ) :
      (∫ ω, sourceTerm j ω ∂μ) ≤ W j * inSourceMeanActual M m (5 + j) t := by
    change (∫ ω, W j * T j ω ∂μ) ≤ _
    rw [integral_const_mul, hmean]
  have hsourceSeries := nonnegative_series_integral_ae' μ sourceTerm
    (fun j => W j * inSourceMeanActual M m (5 + j) t)
    hsourceInt hsourceTermNonneg hsourceAe hsource.1 hsourceCap
  have hsourceSeriesInt : Integrable sourceSeries μ := by
    simpa [sourceSeries] using hsourceSeries.1
  have hsourceSeriesBound :
      (∫ ω, sourceSeries ω ∂μ) ≤
        mixedXiPreCap M + t * mixedBridgeLocalSlope M h m := by
    calc
      _ ≤ ∑' j : ℕ, W j * inSourceMeanActual M m (5 + j) t := by
        simpa [sourceSeries, sourceTerm] using hsourceSeries.2
      _ ≤ _ := hsource.2

  have hglobalTail (j : ℕ) :
      Integrable (fun ω => rareExpansionTail β (Rglobal ω) (T j ω) k.val) μ ∧
      (∫ ω, rareExpansionTail β (Rglobal ω) (T j ω) k.val ∂μ) ≤
        rareExpansionTail β ε (C j) k.val :=
    old_signed_rare_power_tail_payment Rglobal (T j) β ε (C j) k.val
      (by omega) hβ0 hε0 (hC0 j) hRglobal0 (hT0 j)
      hRglobalMeas (hTmeas j) hRglobal128 (hprofile j)
  have hglobalTermInt (j : ℕ) : Integrable (globalRareTerm j) μ := by
    simpa [globalRareTerm] using (hglobalTail j).1.const_mul (W j)
  have hglobalTermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ globalRareTerm j ω := by
    have htail : 0 ≤ rareExpansionTail β (Rglobal ω) (T j ω) k.val := by
      unfold rareExpansionTail
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg hβ0 _)) (pow_nonneg (hRglobal0 ω) _))
        (hT0 j ω)
    exact mul_nonneg (hW0 j) htail
  have hglobalRareAe : ∀ᵐ ω ∂μ,
      Summable (fun j => globalRareTerm j ω) := by
    filter_upwards [htraceAe] with ω hω
    let D : ℝ := rareExpansionTail β (Rglobal ω) 1 k.val
    have hD0 : 0 ≤ D := by
      dsimp [D, rareExpansionTail]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg hβ0 _)) (pow_nonneg (hRglobal0 ω) _)) (by norm_num)
    have hlinear (j : ℕ) :
        rareExpansionTail β (Rglobal ω) (T j ω) k.val = D * T j ω := by
      dsimp [D]
      unfold rareExpansionTail
      simp only [mul_one, Finset.sum_mul]
    have hsum : Summable (fun j : ℕ => α ^ j * T j ω) := by
      simpa [T, μ] using hω
    have hmajor (j : ℕ) : globalRareTerm j ω ≤
        (b₀ * D) * (α ^ j * T j ω) := by
      change W j * rareExpansionTail β (Rglobal ω) (T j ω) k.val ≤ _
      rw [hlinear j]
      calc
        _ ≤ (b₀ * α ^ j) * (D * T j ω) :=
          mul_le_mul_of_nonneg_right (hWle j)
            (mul_nonneg hD0 (hT0 j ω))
        _ = _ := by ring
    have hsum' := Summable.of_nonneg_of_le
      (fun j => hglobalTermNonneg j ω) hmajor (hsum.mul_left (b₀ * D))
    simpa only [globalRareTerm, W, w, b₀, α] using hsum'
  have hglobalCoeffCap (j : ℕ) :
      (∫ ω, globalRareTerm j ω ∂μ) ≤
        W j * (13 * ε * C j) := by
    rw [show globalRareTerm j = fun ω =>
      W j * rareExpansionTail β (Rglobal ω) (T j ω) k.val by rfl,
      integral_const_mul]
    calc
      _ ≤ W j * rareExpansionTail β ε (C j) k.val :=
        mul_le_mul_of_nonneg_left (hglobalTail j).2 (hW0 j)
      _ ≤ W j * (13 * ε * C j) :=
        mul_le_mul_of_nonneg_left
          (rare_tail_thirteen' ε (C j) hε0 hεsmall (hC0 j) k.val
            (by omega)) (hW0 j)
  have hglobalBudget := global_rare_budget M hγ
  have hglobalRareIntBound := nonnegative_series_integral_ae' μ globalRareTerm
    (fun j => W j * (13 * ε * C j)) hglobalTermInt hglobalTermNonneg
    hglobalRareAe hglobalBudget.1 hglobalCoeffCap
  have hglobalRareInt : Integrable globalRare μ := by
    simpa [globalRare] using hglobalRareIntBound.1
  have hglobalRareBound :
      (∫ ω, globalRare ω ∂μ) ≤ (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    calc
      _ ≤ ∑' j : ℕ, W j * (13 * ε * C j) := by
        simpa [globalRare, globalRareTerm] using hglobalRareIntBound.2
      _ ≤ _ := by simpa [W, ε, C] using hglobalBudget.2

  have hbaseAe : ∀ᵐ ω ∂μ, Summable (fun j => baseTerm j ω) := by
    filter_upwards [hsourceAe] with ω hω
    have hs := hω.mul_left (B ω ^ k.val)
    apply hs.congr
    intro j
    dsimp [baseTerm, sourceTerm]
    ring
  have hbaseTermInt (j : ℕ) : Integrable (baseTerm j) μ := by
    have hh := old_signed_rare_history_power_payment B Rglobal (T j)
      β ε (C j) k.val (by omega) hβ0 hε0 (hC0 j)
      hB0 hRglobal0 (hT0 j) hBmeas hRglobalMeas (hTmeas j)
      hBsplit hRglobal128 (hprofile j)
    have heq : baseTerm j = fun ω => W j * (B ω ^ k.val * T j ω) := by
      funext ω
      dsimp [baseTerm]
      ring
    rw [heq]
    exact hh.1.const_mul (W j)
  have hbaseTermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ baseTerm j ω := by
    exact mul_nonneg (mul_nonneg (hW0 j) (pow_nonneg (hB0 ω) k.val))
      (hT0 j ω)
  have hbaseCoeffSummable : Summable (fun j : ℕ =>
      β ^ k.val * (W j * inSourceMeanActual M m (5 + j) t) +
        W j * (13 * ε * C j)) := by
    have hfirst := hsource.1.mul_left (β ^ k.val)
    have hsecond : Summable (fun j : ℕ => W j * (13 * ε * C j)) := by
      simpa [W, ε, C] using hglobalBudget.1
    apply hfirst.add hsecond |>.congr
    intro j
    ring
  have hbaseTermCap (j : ℕ) :
      (∫ ω, baseTerm j ω ∂μ) ≤
        β ^ k.val * (W j * inSourceMeanActual M m (5 + j) t) +
          W j * (13 * ε * C j) := by
    have hh := old_signed_rare_history_power_payment B Rglobal (T j)
      β ε (C j) k.val (by omega) hβ0 hε0 (hC0 j)
      hB0 hRglobal0 (hT0 j) hBmeas hRglobalMeas (hTmeas j)
      hBsplit hRglobal128 (hprofile j)
    have htail := rare_tail_thirteen' ε (C j) hε0 hεsmall
      (hC0 j) k.val (by omega)
    have heq : baseTerm j = fun ω => W j * (B ω ^ k.val * T j ω) := by
      funext ω
      dsimp [baseTerm]
      ring
    rw [heq, integral_const_mul]
    calc
      _ ≤ W j * (β ^ k.val * (∫ ω, T j ω ∂μ) +
          rareExpansionTail β ε (C j) k.val) :=
        mul_le_mul_of_nonneg_left hh.2 (hW0 j)
      _ ≤ W j * (β ^ k.val * inSourceMeanActual M m (5 + j) t +
          13 * ε * C j) := by
        apply mul_le_mul_of_nonneg_left _ (hW0 j)
        rw [hmean]
        simpa [add_comm] using
          (add_le_add_left htail
            (β ^ k.val * inSourceMeanActual M m (5 + j) t))
      _ = _ := by ring
  have hbaseIntegral := nonnegative_series_integral_ae' μ baseTerm
    (fun j => β ^ k.val * (W j * inSourceMeanActual M m (5 + j) t) +
      W j * (13 * ε * C j))
    hbaseTermInt hbaseTermNonneg hbaseAe hbaseCoeffSummable hbaseTermCap
  have hbaseInt : Integrable baseSeries μ := by
    simpa [baseSeries] using hbaseIntegral.1

  have hbasePointwise : ∀ᵐ ω ∂μ,
      baseSeries ω ≤ β ^ k.val * sourceSeries ω + globalRare ω := by
    filter_upwards [hBsplit, hsourceAe, hglobalRareAe, hbaseAe] with
      ω hBω hsourceω hrareω hbaseω
    have hterm (j : ℕ) : baseTerm j ω ≤
        β ^ k.val * sourceTerm j ω + globalRareTerm j ω := by
      have hX0 : 0 ≤ T j ω := hT0 j ω
      have hexp := rare_factor_pointwise_expansion (B ω) β (Rglobal ω)
        (T j ω) k.val (hB0 ω) hX0 hBω (by omega)
      calc
        _ = W j * (B ω ^ k.val * T j ω) := by
          dsimp [baseTerm]
          ring
        _ ≤ W j * (β ^ k.val * T j ω +
            rareExpansionTail β (Rglobal ω) (T j ω) k.val) :=
          mul_le_mul_of_nonneg_left hexp (hW0 j)
        _ = β ^ k.val * sourceTerm j ω + globalRareTerm j ω := by
          dsimp [sourceTerm, globalRareTerm]
          ring
    have hsumRhs : Summable (fun j : ℕ =>
        β ^ k.val * sourceTerm j ω + globalRareTerm j ω) :=
      (hsourceω.mul_left (β ^ k.val)).add hrareω
    have hsum := Summable.tsum_le_tsum hterm hbaseω hsumRhs
    dsimp [baseSeries, sourceSeries, globalRare]
    rw [(hsourceω.mul_left (β ^ k.val)).tsum_add hrareω,
      tsum_mul_left] at hsum
    exact hsum
  have hbaseMajorInt :
      Integrable (fun ω => β ^ k.val * sourceSeries ω + globalRare ω) μ :=
    (hsourceSeriesInt.const_mul (β ^ k.val)).add hglobalRareInt
  have hbaseBound :
      (∫ ω, baseSeries ω ∂μ) ≤
        β ^ k.val * (mixedXiPreCap M +
          t * mixedBridgeLocalSlope M h m) +
          β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    calc
      _ ≤ ∫ ω, β ^ k.val * sourceSeries ω + globalRare ω ∂μ :=
        integral_mono_ae hbaseInt hbaseMajorInt hbasePointwise
      _ = β ^ k.val * (∫ ω, sourceSeries ω ∂μ) +
          ∫ ω, globalRare ω ∂μ := by
        rw [integral_add (hsourceSeriesInt.const_mul _) hglobalRareInt,
          integral_const_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left hsourceSeriesBound (pow_nonneg hβ0 k.val))
        (calc
          (∫ ω, globalRare ω ∂μ) ≤ (1 / (13 * 10 ^ 12 : ℝ)) * theta M :=
            hglobalRareBound
          _ ≤ β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
            have hpow : 1 ≤ β ^ k.val := one_le_pow₀ hβ1
            have hreserve : 0 ≤ (1 / (13 * 10 ^ 12 : ℝ)) * theta M :=
              mul_nonneg (by norm_num) hθ
            calc
              _ = 1 * ((1 / (13 * 10 ^ 12 : ℝ)) * theta M) := by ring
              _ ≤ β ^ k.val * ((1 / (13 * 10 ^ 12 : ℝ)) * theta M) :=
                mul_le_mul_of_nonneg_right hpow hreserve
              _ = _ := by ring)

  have hlocalBlock (j : ℕ) := local_union_depth_block
    M h hM hγ N hpast m hm t ht j
  have hRlocal0 (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ Rlocal j ω := by
    change 0 ≤ positiveSplitRemainder _ _ _
    exact (positive_split _ _ _).1
  have hRlocalMeas (j : ℕ) : AEStronglyMeasurable (Rlocal j) μ :=
    (hlocalBlock j).remainder_measurable.aestronglyMeasurable
  have hRlocal128 (j : ℕ) :
      eLpNorm (Rlocal j) 128 μ ≤ ENNReal.ofReal (epsLocal j) := by
    change eLpNorm
      (inverseBankDepthBlockRemainder .localInverse
        (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) j) 128 μ ≤ _
    exact (hlocalBlock j).remainder_L128
  have hlocalEps0 (j : ℕ) : 0 ≤ epsLocal j := by
    unfold epsLocal inverseBankDepthReserve inverseBankReserve bankDepthFrame
    positivity
  have hlocalDiscount (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      α ^ j * Rlocal j ω ≤ B ω := by
    simpa [Rlocal, B, α] using
      mixed_old_local_depth_remainder_discount_le_global M m t ht j ω
  have hlocalRareAe : ∀ᵐ ω ∂μ, Summable (fun j => localTerm j ω) := by
    have hs := weighted_rare_series_summable_ae μ α B Rlocal T k.val
      hα0 hα1 hB0 hRlocal0 hT0 hlocalDiscount htraceAe
    simpa [localTerm, w, α] using hs
  have hlocalTermInt (j : ℕ) : Integrable (localTerm j) μ := by
    have hh := correlated_B_power_R_trace_integrable B (Rlocal j) (T j)
      β (epsLocal j) (C j) k.val (by omega) hβ0 (hlocalEps0 j) (hC0 j)
      hB0 (hRlocal0 j) (hT0 j) hBmeas (hRlocalMeas j) (hTmeas j)
      hB128 (hRlocal128 j) (hprofile j)
    have heq : localTerm j = fun ω => w j *
        (B ω ^ k.val * Rlocal j ω * T j ω) := by
      funext ω
      dsimp [localTerm]
      ring
    rw [heq]
    exact hh.1.const_mul (w j)
  have hw0 (j : ℕ) : 0 ≤ w j := by
    dsimp [w]
    exact mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα0 hα1))
      (pow_nonneg hα0 _)
  have hlocalTermNonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ localTerm j ω := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw0 j)
      (pow_nonneg (hB0 ω) k.val)) (hRlocal0 j ω)) (hT0 j ω)
  have hlocalCoeffSummable : Summable (fun j : ℕ =>
      w j * (β ^ k.val * epsLocal j * C j)) := by
    have hbase := old_signed_depth_rare_summable M hγ
    have hscale := hbase.mul_left ((1 - α ^ 2) * β ^ k.val)
    apply hscale.congr
    intro j
    simp only [w, epsLocal, C, α, rawWeakTraceProfileEnvelope,
      inverseBankDepthReserve, pow_mul]
    ring
  have hlocalCoeffBound :
      (∑' j : ℕ, w j * (β ^ k.val * epsLocal j * C j)) ≤
        β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    have hbudget := old_signed_directional_rare_delta M hγ
    have hsum0 : 0 ≤ ∑' j : ℕ, α ^ (2 * j) * epsLocal j * C j :=
      tsum_nonneg (fun j => mul_nonneg
        (mul_nonneg (pow_nonneg hα0 _) (hlocalEps0 j)) (hC0 j))
    have hraw : 13 * ((1 - α ^ 2) *
        (∑' j : ℕ, α ^ (2 * j) * epsLocal j * C j)) ≤
        (1 / 10 ^ 12 : ℝ) * theta M := by
      simpa [C, epsLocal, α, rawWeakTraceProfileEnvelope,
        inverseBankDepthReserve, pow_mul, mul_assoc, mul_left_comm, mul_comm] using hbudget
    have hbase : (1 - α ^ 2) *
        (∑' j : ℕ, α ^ (2 * j) * epsLocal j * C j) ≤
          (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
      have hscaled := mul_le_mul_of_nonneg_left hraw
        (by norm_num : (0 : ℝ) ≤ 1 / 13)
      calc
        _ = (1 / 13 : ℝ) * (13 * ((1 - α ^ 2) *
            (∑' j : ℕ, α ^ (2 * j) * epsLocal j * C j))) := by ring
        _ ≤ (1 / 13 : ℝ) * ((1 / 10 ^ 12 : ℝ) * theta M) := hscaled
        _ = (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by ring
    have hident : (∑' j : ℕ, w j *
        (β ^ k.val * epsLocal j * C j)) =
        β ^ k.val * ((1 - α ^ 2) *
          (∑' j : ℕ, α ^ (2 * j) * epsLocal j * C j)) := by
      calc
        _ = ∑' j : ℕ, ((1 - α ^ 2) * β ^ k.val) *
            (α ^ (2 * j) * epsLocal j * C j) := by
          apply tsum_congr
          intro j
          simp only [w]
          ring
        _ = _ := by rw [tsum_mul_left]; ring
    rw [hident]
    calc
      _ ≤ β ^ k.val * ((1 / (13 * 10 ^ 12 : ℝ)) * theta M) :=
        mul_le_mul_of_nonneg_left hbase (pow_nonneg hβ0 k.val)
      _ = _ := by ring
  have hlocalTermCap (j : ℕ) :
      (∫ ω, localTerm j ω ∂μ) ≤
        w j * (β ^ k.val * epsLocal j * C j) := by
    have hh := correlated_B_power_R_trace_integrable B (Rlocal j) (T j)
      β (epsLocal j) (C j) k.val (by omega) hβ0 (hlocalEps0 j) (hC0 j)
      hB0 (hRlocal0 j) (hT0 j) hBmeas (hRlocalMeas j) (hTmeas j)
      hB128 (hRlocal128 j) (hprofile j)
    have heq : localTerm j = fun ω => w j *
        (B ω ^ k.val * Rlocal j ω * T j ω) := by
      funext ω
      dsimp [localTerm]
      ring
    rw [heq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hh.2 (hw0 j)
  have hlocalIntegral := nonnegative_series_integral_ae' μ localTerm
    (fun j => w j * (β ^ k.val * epsLocal j * C j))
    hlocalTermInt hlocalTermNonneg hlocalRareAe hlocalCoeffSummable hlocalTermCap
  have hlocalInt : Integrable localSeries μ := by
    simpa [localSeries] using hlocalIntegral.1
  have hlocalBound :
      (∫ ω, localSeries ω ∂μ) ≤
        β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    calc
      _ ≤ ∑' j : ℕ, w j * (β ^ k.val * epsLocal j * C j) := by
        simpa [localSeries, localTerm] using hlocalIntegral.2
      _ ≤ _ := hlocalCoeffBound

  have hthetaDecomp : ∀ᵐ ω ∂μ,
      B ω ^ k.val * mixedOldTheta M m U t ω =
        baseSeries ω + localSeries ω := by
    filter_upwards [hbaseAe, hlocalRareAe] with ω hbaseω hlocalω
    have hterm (j : ℕ) :
        B ω ^ k.val * mixedOldThetaTerm M m U t j ω =
          baseTerm j ω + localTerm j ω := by
      dsimp [mixedOldThetaTerm, mixedDepthTraceAverage]
      rw [mixed_old_depth_coefficient_formula]
      dsimp [baseTerm, localTerm, W, w, α, T, Rlocal,
        mixedBridgeOldInverseBaseline, mixedDepthTraceAverage]
      simp [mixedBridgeLocalWeight, mixedBridgeOldInverseBaseline]
      ring
    calc
      _ = ∑' j : ℕ, B ω ^ k.val *
          mixedOldThetaTerm M m U t j ω := by
        simp [mixedOldTheta, tsum_mul_left]
      _ = ∑' j : ℕ, (baseTerm j ω + localTerm j ω) := by
        apply tsum_congr
        exact hterm
      _ = baseSeries ω + localSeries ω := hbaseω.tsum_add hlocalω
  have hsumInt : Integrable (fun ω => baseSeries ω + localSeries ω) μ :=
    hbaseInt.add hlocalInt
  have hthetaReverse :
      (fun ω => baseSeries ω + localSeries ω) =ᵐ[μ]
        (fun ω => B ω ^ k.val * mixedOldTheta M m U t ω) := by
    filter_upwards [hthetaDecomp] with ω hω
    exact hω.symm
  have htargetInt : Integrable
      (fun ω => B ω ^ k.val * mixedOldTheta M m U t ω) μ :=
    hsumInt.congr hthetaReverse
  have htargetIntegral :
      (∫ ω, B ω ^ k.val * mixedOldTheta M m U t ω ∂μ) =
        (∫ ω, baseSeries ω ∂μ) + (∫ ω, localSeries ω ∂μ) := by
    rw [integral_congr_ae hthetaDecomp, integral_add hbaseInt hlocalInt]
  have hreserve :
      (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
        (1 / (13 * 10 ^ 12 : ℝ)) * theta M ≤
          (1 / 10 ^ 12 : ℝ) * theta M := by
    nlinarith [hθ]
  have hfinal :
      (∫ ω, B ω ^ k.val * mixedOldTheta M m U t ω ∂μ) ≤
        β ^ k.val * (mixedXiPreCap M +
          (1 / 10 ^ 12 : ℝ) * theta M +
          t * mixedBridgeLocalSlope M h m) := by
    rw [htargetIntegral]
    calc
      _ ≤ β ^ k.val * (mixedXiPreCap M +
          t * mixedBridgeLocalSlope M h m) +
            β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
            β ^ k.val * (1 / (13 * 10 ^ 12 : ℝ)) * theta M :=
        add_le_add hbaseBound hlocalBound
      _ = β ^ k.val *
          (mixedXiPreCap M + t * mixedBridgeLocalSlope M h m +
            (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
            (1 / (13 * 10 ^ 12 : ℝ)) * theta M) := by ring
      _ ≤ β ^ k.val *
          (mixedXiPreCap M + t * mixedBridgeLocalSlope M h m +
            (1 / 10 ^ 12 : ℝ) * theta M) := by
        have hfactor :
            mixedXiPreCap M + t * mixedBridgeLocalSlope M h m +
              (1 / (13 * 10 ^ 12 : ℝ)) * theta M +
              (1 / (13 * 10 ^ 12 : ℝ)) * theta M ≤
            mixedXiPreCap M + t * mixedBridgeLocalSlope M h m +
              (1 / 10 ^ 12 : ℝ) * theta M := by
          linarith [hreserve]
        exact mul_le_mul_of_nonneg_left hfactor (pow_nonneg hβ0 k.val)
      _ = _ := by ring
  exact ⟨htargetInt, by simpa [B, β] using hfinal⟩

end
end ASDExplicitGamma.Inverse
