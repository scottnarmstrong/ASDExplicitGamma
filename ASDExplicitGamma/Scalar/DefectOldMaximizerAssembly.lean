module

public import ASDExplicitGamma.Inverse.RawRareExpansion
public import ASDExplicitGamma.Inverse.ParentGapHolder
public import ASDExplicitGamma.Native.OldSignedRarePowerPayment
public import ASDExplicitGamma.Native.OldSignedBankRareHistory

/-! Abstract correlated rare assembly: `E[B^k Σ_j w_j D_j T_j]` against the
baseline series, the global rare payment and the local rare payment. Every
input is a structural property of `B`, `D_j`, `T_j`; there is no moment row. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Native
noncomputable section

theorem nonneg_series_integral_ae'
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

theorem rare_tail_thirteen
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
  have hscalar :
      rareExpansionTail (14103 / 10000 : ℝ) ε 1 k ≤ 13 * ε := by
    interval_cases k <;>
      norm_num [rareExpansionTail, Finset.sum_Icc_succ_top, Nat.choose] <;>
      nlinarith [hε, hε2, hε3]
  rw [old_signed_rare_tail_linear (14103 / 10000 : ℝ) ε C k]
  exact mul_le_mul_of_nonneg_right hscalar hC

theorem BkRT_integrable
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


theorem rare_assembly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α ε0 : ℝ) (k : ℕ) (hk : k ≤ 3) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hε0 : 0 ≤ ε0) (hε0s : ε0 ≤ 1 / 1000)
    (B R : Ω → ℝ) (T D e : ℕ → Ω → ℝ) (b r C : ℕ → ℝ) (K : ℝ)
    (hB0 : ∀ ω, 0 ≤ B ω) (hBm : AEStronglyMeasurable B μ)
    (hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal (14103 / 10000))
    (hBsplit : ∀ᵐ ω ∂μ, B ω ≤ 14103 / 10000 + R ω)
    (hR0 : ∀ ω, 0 ≤ R ω) (hRm : AEStronglyMeasurable R μ)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε0)
    (hT0 : ∀ j ω, 0 ≤ T j ω) (hTm : ∀ j, AEStronglyMeasurable (T j) μ)
    (hT2 : ∀ j, eLpNorm (T j) 2 μ ≤ ENNReal.ofReal (C j)) (hC0 : ∀ j, 0 ≤ C j)
    (hD0 : ∀ j ω, 0 ≤ D j ω) (hDm : ∀ j, AEStronglyMeasurable (D j) μ)
    (he0 : ∀ j ω, 0 ≤ e j ω) (hem : ∀ j, AEStronglyMeasurable (e j) μ)
    (he128 : ∀ j, eLpNorm (e j) 128 μ ≤ ENNReal.ofReal (r j)) (hr0 : ∀ j, 0 ≤ r j)
    (hb0 : ∀ j, 0 ≤ b j) (hbK : ∀ j, α ^ j * b j ≤ K)
    (hDsplit : ∀ᵐ ω ∂μ, ∀ j, D j ω ≤ b j + e j ω)
    (hαD : ∀ j ω, α ^ j * D j ω ≤ B ω) (hαe : ∀ j ω, α ^ j * e j ω ≤ B ω)
    (hTsum : ∀ᵐ ω ∂μ, Summable (fun j => α ^ j * T j ω))
    (hGsum : Summable (fun j => (1 - α ^ 2) * α ^ (2 * j) * b j * (13 * ε0 * C j)))
    (hLsum : Summable (fun j => (1 - α ^ 2) * α ^ (2 * j) *
      ((14103 / 10000 : ℝ) ^ k * r j * C j)))
    (hbase : Summable (fun j => (1 - α ^ 2) * α ^ (2 * j) * b j * ∫ ω, T j ω ∂μ)) :
    Integrable (fun ω => B ω ^ k *
      ∑' j, (1 - α ^ 2) * α ^ (2 * j) * D j ω * T j ω) μ ∧
    (∫ ω, B ω ^ k * ∑' j, (1 - α ^ 2) * α ^ (2 * j) * D j ω * T j ω ∂μ) ≤
      (14103 / 10000 : ℝ) ^ k *
          (∑' j, (1 - α ^ 2) * α ^ (2 * j) * b j * ∫ ω, T j ω ∂μ) +
        (∑' j, (1 - α ^ 2) * α ^ (2 * j) * b j * (13 * ε0 * C j)) +
        (∑' j, (1 - α ^ 2) * α ^ (2 * j) * ((14103 / 10000 : ℝ) ^ k * r j * C j)) := by
  classical
  set β : ℝ := 14103 / 10000 with hβdef
  have hβ0 : 0 ≤ β := by norm_num [hβdef]
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, ∀ j, w j = (1 - α ^ 2) * α ^ (2 * j) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hw] at hGsum hLsum hbase ⊢
  have hΔ0 : 0 ≤ 1 - α ^ 2 := sub_nonneg.mpr (pow_le_one₀ hα0 hα1)
  have hw0 (j : ℕ) : 0 ≤ w j := by rw [hw]; exact mul_nonneg hΔ0 (pow_nonneg hα0 _)
  have hwsplit (j : ℕ) : w j = (1 - α ^ 2) * (α ^ j * α ^ j) := by
    rw [hw, show 2 * j = j + j by omega, pow_add]
  have hTmem (j : ℕ) : MemLp (T j) 2 μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt (hT2 j) ENNReal.ofReal_lt_top
  have hTint (j : ℕ) : Integrable (T j) μ := (hTmem j).integrable (by norm_num)
  have hαpow0 (j : ℕ) : 0 ≤ α ^ j := pow_nonneg hα0 j
  have hBk0 (ω : Ω) : 0 ≤ B ω ^ k := pow_nonneg (hB0 ω) k
  let base : ℕ → Ω → ℝ := fun j ω => w j * b j * T j ω
  let rareG : ℕ → Ω → ℝ := fun j ω =>
    w j * b j * rareExpansionTail β (R ω) (T j ω) k
  let loc : ℕ → Ω → ℝ := fun j ω => w j * (B ω ^ k * e j ω * T j ω)
  have hD1nn (ω : Ω) : 0 ≤ rareExpansionTail β (R ω) 1 k := by
    unfold rareExpansionTail
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (mul_nonneg
      (Nat.cast_nonneg _) (pow_nonneg hβ0 _)) (pow_nonneg (hR0 ω) _)) (by norm_num))
  have hrareNN (j : ℕ) (ω : Ω) : 0 ≤ rareG j ω := by
    show 0 ≤ w j * b j * rareExpansionTail β (R ω) (T j ω) k
    rw [old_signed_rare_tail_linear β (R ω) (T j ω) k]
    exact mul_nonneg (mul_nonneg (hw0 j) (hb0 j)) (mul_nonneg (hD1nn ω) (hT0 j ω))
  have hbaseNN (j : ℕ) (ω : Ω) : 0 ≤ base j ω :=
    mul_nonneg (mul_nonneg (hw0 j) (hb0 j)) (hT0 j ω)
  have hlocNN (j : ℕ) (ω : Ω) : 0 ≤ loc j ω :=
    mul_nonneg (hw0 j) (mul_nonneg (mul_nonneg (hBk0 ω) (he0 j ω)) (hT0 j ω))
  -- almost-everywhere summability
  have hbaseAe : ∀ᵐ ω ∂μ, Summable (fun j => base j ω) := by
    filter_upwards [hTsum] with ω hω
    refine Summable.of_nonneg_of_le (fun j => hbaseNN j ω) (fun j => ?_)
      (hω.mul_left ((1 - α ^ 2) * K))
    have : base j ω = (1 - α ^ 2) * (α ^ j * b j) * (α ^ j * T j ω) := by
      simp only [base]; rw [hwsplit j]; ring
    rw [this]
    have h1 : α ^ j * b j ≤ K := hbK j
    have h2 : 0 ≤ α ^ j * T j ω := mul_nonneg (hαpow0 j) (hT0 j ω)
    calc _ ≤ (1 - α ^ 2) * K * (α ^ j * T j ω) := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul_of_nonneg_left h1 hΔ0
      _ = _ := by ring
  have hrareAe : ∀ᵐ ω ∂μ, Summable (fun j => rareG j ω) := by
    filter_upwards [hTsum] with ω hω
    refine Summable.of_nonneg_of_le (fun j => hrareNN j ω) (fun j => ?_)
      (hω.mul_left ((1 - α ^ 2) * K * rareExpansionTail β (R ω) 1 k))
    have : rareG j ω = (1 - α ^ 2) * rareExpansionTail β (R ω) 1 k *
        (α ^ j * b j) * (α ^ j * T j ω) := by
      simp only [rareG]; rw [old_signed_rare_tail_linear β (R ω) (T j ω) k, hwsplit j]; ring
    rw [this]
    have h1 : α ^ j * b j ≤ K := hbK j
    have h2 : 0 ≤ α ^ j * T j ω := mul_nonneg (hαpow0 j) (hT0 j ω)
    have h3 := hD1nn ω
    calc _ = ((1 - α ^ 2) * rareExpansionTail β (R ω) 1 k) * (α ^ j * b j) *
          (α ^ j * T j ω) := by ring
      _ ≤ ((1 - α ^ 2) * rareExpansionTail β (R ω) 1 k) * K * (α ^ j * T j ω) := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hΔ0 h3)
      _ = _ := by ring
  have hlocAe : ∀ᵐ ω ∂μ, Summable (fun j => loc j ω) := by
    filter_upwards [hTsum] with ω hω
    refine Summable.of_nonneg_of_le (fun j => hlocNN j ω) (fun j => ?_)
      (hω.mul_left ((1 - α ^ 2) * B ω ^ (k + 1)))
    have : loc j ω = (1 - α ^ 2) * B ω ^ k * (α ^ j * e j ω) * (α ^ j * T j ω) := by
      simp only [loc]; rw [hwsplit j]; ring
    rw [this]
    have h2 : 0 ≤ α ^ j * T j ω := mul_nonneg (hαpow0 j) (hT0 j ω)
    calc _ ≤ (1 - α ^ 2) * B ω ^ k * B ω * (α ^ j * T j ω) := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul_of_nonneg_left (hαe j ω) (mul_nonneg hΔ0 (hBk0 ω))
      _ = _ := by rw [pow_succ]; ring
  have hLHSsum : ∀ ω, Summable (fun j => α ^ j * T j ω) →
      Summable (fun j => B ω ^ k * (w j * D j ω * T j ω)) := by
    intro ω hω
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hBk0 ω)
      (mul_nonneg (mul_nonneg (hw0 j) (hD0 j ω)) (hT0 j ω))) (fun j => ?_)
      (hω.mul_left ((1 - α ^ 2) * B ω ^ (k + 1)))
    have : B ω ^ k * (w j * D j ω * T j ω) =
        (1 - α ^ 2) * B ω ^ k * (α ^ j * D j ω) * (α ^ j * T j ω) := by
      rw [hwsplit j]; ring
    rw [this]
    have h2 : 0 ≤ α ^ j * T j ω := mul_nonneg (hαpow0 j) (hT0 j ω)
    calc _ ≤ (1 - α ^ 2) * B ω ^ k * B ω * (α ^ j * T j ω) := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul_of_nonneg_left (hαD j ω) (mul_nonneg hΔ0 (hBk0 ω))
      _ = _ := by rw [pow_succ]; ring
  -- pointwise term bound
  have hterm : ∀ᵐ ω ∂μ, ∀ j, B ω ^ k * (w j * D j ω * T j ω) ≤
      β ^ k * base j ω + rareG j ω + loc j ω := by
    filter_upwards [hBsplit, hDsplit] with ω hBω hDω j
    have hX0 : 0 ≤ b j * T j ω := mul_nonneg (hb0 j) (hT0 j ω)
    have hexp := rare_factor_pointwise_expansion (B ω) β (R ω) (b j * T j ω) k
      (hB0 ω) hX0 hBω hk
    have hlin : rareExpansionTail β (R ω) (b j * T j ω) k =
        b j * rareExpansionTail β (R ω) (T j ω) k := by
      rw [old_signed_rare_tail_linear β (R ω) (b j * T j ω) k,
        old_signed_rare_tail_linear β (R ω) (T j ω) k]; ring
    have hcore : B ω ^ k * (D j ω * T j ω) ≤
        β ^ k * (b j * T j ω) + b j * rareExpansionTail β (R ω) (T j ω) k +
          B ω ^ k * e j ω * T j ω := by
      have h1 : D j ω * T j ω ≤ (b j + e j ω) * T j ω :=
        mul_le_mul_of_nonneg_right (hDω j) (hT0 j ω)
      have h2 := mul_le_mul_of_nonneg_left h1 (hBk0 ω)
      rw [hlin] at hexp
      nlinarith [h2, hexp]
    calc B ω ^ k * (w j * D j ω * T j ω) = w j * (B ω ^ k * (D j ω * T j ω)) := by ring
      _ ≤ w j * (β ^ k * (b j * T j ω) + b j * rareExpansionTail β (R ω) (T j ω) k +
          B ω ^ k * e j ω * T j ω) := mul_le_mul_of_nonneg_left hcore (hw0 j)
      _ = _ := by simp only [base, rareG, loc]; ring
  -- integral bounds of the three series
  have hBaseInt := nonneg_series_integral_ae' μ base
    (fun j => w j * b j * ∫ ω, T j ω ∂μ)
    (fun j => (hTint j).const_mul (w j * b j)) hbaseNN hbaseAe hbase
    (fun j => by
      simp only [base]; rw [integral_const_mul])
  have hrareTail (j : ℕ) := old_signed_rare_power_tail_payment (μ := μ) R (T j) β ε0 (C j) k
    (by omega) hβ0 hε0 (hC0 j) hR0 (hT0 j) hRm (hTm j) hR128 (hT2 j)
  have hRareInt := nonneg_series_integral_ae' μ rareG
    (fun j => w j * b j * (13 * ε0 * C j))
    (fun j => by
      have := (hrareTail j).1.const_mul (w j * b j)
      simpa only [rareG] using this)
    hrareNN hrareAe hGsum
    (fun j => by
      simp only [rareG]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        ((hrareTail j).2.trans (rare_tail_thirteen ε0 (C j) hε0 hε0s (hC0 j) k hk))
        (mul_nonneg (hw0 j) (hb0 j)))
  have hlocB (j : ℕ) := BkRT_integrable (μ := μ) B (e j) (T j) β (r j) (C j) k hk
    hβ0 (hr0 j) (hC0 j) hB0 (he0 j) (hT0 j) hBm (hem j) (hTm j) hB128 (he128 j) (hT2 j)
  have hLocInt := nonneg_series_integral_ae' μ loc
    (fun j => w j * (β ^ k * r j * C j))
    (fun j => (hlocB j).1.const_mul (w j)) hlocNN hlocAe hLsum
    (fun j => by
      simp only [loc]; rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hlocB j).2 (hw0 j))
  -- the majorant
  set G : Ω → ℝ := fun ω => β ^ k * (∑' j, base j ω) + (∑' j, rareG j ω) +
    (∑' j, loc j ω) with hG
  have hGint : Integrable G μ :=
    ((hBaseInt.1.const_mul (β ^ k)).add hRareInt.1).add hLocInt.1
  have hFeq (ω : Ω) : B ω ^ k * ∑' j, w j * D j ω * T j ω =
      ∑' j, B ω ^ k * (w j * D j ω * T j ω) := by rw [tsum_mul_left]
  have hFle : ∀ᵐ ω ∂μ, B ω ^ k * ∑' j, w j * D j ω * T j ω ≤ G ω := by
    filter_upwards [hterm, hbaseAe, hrareAe, hlocAe, hTsum] with ω h1 h2 h3 h4 h5
    rw [hFeq ω]
    have hs1 := hLHSsum ω h5
    have hs2 : Summable (fun j => β ^ k * base j ω + rareG j ω + loc j ω) :=
      ((h2.mul_left (β ^ k)).add h3).add h4
    calc _ ≤ ∑' j, (β ^ k * base j ω + rareG j ω + loc j ω) := hs1.tsum_le_tsum h1 hs2
      _ = _ := by
        rw [Summable.tsum_add ((h2.mul_left (β ^ k)).add h3) h4,
          Summable.tsum_add (h2.mul_left (β ^ k)) h3, tsum_mul_left]
  have hF0 (ω : Ω) : 0 ≤ B ω ^ k * ∑' j, w j * D j ω * T j ω :=
    mul_nonneg (hBk0 ω) (tsum_nonneg fun j =>
      mul_nonneg (mul_nonneg (hw0 j) (hD0 j ω)) (hT0 j ω))
  have hFmeas : AEStronglyMeasurable
      (fun ω => B ω ^ k * ∑' j, w j * D j ω * T j ω) μ := by
    have hterms (j : ℕ) : AEStronglyMeasurable
        (fun ω => B ω ^ k * (w j * D j ω * T j ω)) μ :=
      (hBm.pow k).mul ((((hDm j).const_mul (w j)).mul (hTm j)))
    have := aestronglyMeasurable_of_tendsto_ae (μ := μ) Filter.atTop
      (f := fun s : Finset ℕ => fun ω => ∑ j ∈ s, B ω ^ k * (w j * D j ω * T j ω))
      (g := fun ω => ∑' j, B ω ^ k * (w j * D j ω * T j ω))
      (fun s => s.aestronglyMeasurable_fun_sum (fun j _ => hterms j))
      (by
        filter_upwards [hTsum] with ω hω
        exact (hLHSsum ω hω).hasSum)
    simpa only [hFeq] using this
  have hFint : Integrable (fun ω => B ω ^ k * ∑' j, w j * D j ω * T j ω) μ := by
    refine hGint.mono' hFmeas ?_
    filter_upwards [hFle] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
    exact hω
  refine ⟨hFint, ?_⟩
  calc (∫ ω, B ω ^ k * ∑' j, w j * D j ω * T j ω ∂μ) ≤ ∫ ω, G ω ∂μ :=
        integral_mono_ae hFint hGint hFle
    _ = β ^ k * (∫ ω, ∑' j, base j ω ∂μ) + (∫ ω, ∑' j, rareG j ω ∂μ) +
          (∫ ω, ∑' j, loc j ω ∂μ) := by
        have hA : Integrable (fun ω => β ^ k * (∑' j, base j ω) + (∑' j, rareG j ω)) μ :=
          (hBaseInt.1.const_mul (β ^ k)).add hRareInt.1
        have e1 := integral_add hA hLocInt.1
        have e2 := integral_add (hBaseInt.1.const_mul (β ^ k)) hRareInt.1
        simp only [hG]
        rw [e1, e2, integral_const_mul]
    _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_left hBaseInt.2 (pow_nonneg hβ0 k)
        linarith [hRareInt.2, hLocInt.2]

end
end ASDExplicitGamma.Scalar
