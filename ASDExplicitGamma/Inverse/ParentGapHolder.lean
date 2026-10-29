module

public import ASDExplicitGamma.Inverse.RawParentGapInputs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Hölder control for the parent-gap rare products. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory
open scoped NNReal ENNReal

private theorem parent_gap_fin4_cutoff_product
    {α : Type*} [CommMonoidWithZero α] (x y : α) (k : ℕ) (hk : k ≤ 3) :
    (∏ i : Fin 4, if i.val < k then x else if i.val = k then y else 1) =
      x ^ k * y := by
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkcases with rfl | rfl | rfl | rfl
  · simp
  · simp [Fin.prod_univ_succ]
  · simp [Fin.prod_univ_succ, pow_succ, mul_assoc]
  · simp [Fin.prod_univ_succ, pow_succ, mul_assoc]

/-- On a probability space, an `L²` trace pairs with any product of at most
four `L¹²⁸` rare bank factors. -/
theorem parent_gap_rare_trace_holder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (ε C : ℝ) (n : ℕ) (hn : n ≤ 4)
    (hε : 0 ≤ ε)
    (hR0 : ∀ ω, 0 ≤ R ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (hRmeas : AEStronglyMeasurable R μ) (hTmeas : AEStronglyMeasurable T μ)
    (hR128 : eLpNorm R (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    ∫⁻ ω, (ENNReal.ofReal (R ω)) ^ n * ENNReal.ofReal (T ω) ∂μ ≤
      ENNReal.ofReal (ε ^ n * C) := by
  let S : Finset (Fin 2) := Finset.univ
  let F : Fin 2 → Ω → ℝ≥0∞ := fun i ω =>
    if i = 0 then ENNReal.ofReal (R ω) ^ (128 : ℝ) else 1
  let p : Fin 2 → ℝ := fun i =>
    if i = 0 then (n : ℝ) / 128 else (1 / 2 : ℝ) - (n : ℝ) / 128
  let G : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (T ω) ^ (2 : ℝ)
  have hnreal : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  have hp_nonneg : ∀ i ∈ S, 0 ≤ p i := by
    intro i hi
    fin_cases i
    · simp [p]
      positivity
    · simp [p]
      linarith
  have hp_sum : (1 / 2 : ℝ) + ∑ i ∈ S, p i = 1 := by
    simp [S, p, Fin.sum_univ_succ]
    ring
  have hRof : AEMeasurable (fun ω => ENNReal.ofReal (R ω)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable hRmeas.aemeasurable
  have hTof : AEMeasurable (fun ω => ENNReal.ofReal (T ω)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable hTmeas.aemeasurable
  have hFmeas : ∀ i ∈ S, AEMeasurable (F i) μ := by
    intro i hi
    fin_cases i
    · change AEMeasurable (fun ω => ENNReal.ofReal (R ω) ^ (128 : ℝ)) μ
      exact hRof.pow_const _
    · simp [F]
  have hGmeas : AEMeasurable G μ := by
    change AEMeasurable (fun ω => ENNReal.ofReal (T ω) ^ (2 : ℝ)) μ
    exact hTof.pow_const _
  have hholder := ENNReal.lintegral_mul_prod_norm_pow_le
    (s := S) (g := G) (f := F) hGmeas hFmeas (1 / 2 : ℝ) (p := p)
    hp_sum (by norm_num) hp_nonneg
  have hRpow :
      (eLpNorm R (128 : ℝ≥0) μ) ^ (128 : ℝ) =
        ∫⁻ ω, ‖R ω‖ₑ ^ (128 : ℝ) ∂μ := by
    exact eLpNorm_nnreal_pow_eq_lintegral (f := R) (p := (128 : ℝ≥0))
      (by norm_num) hRmeas
  have hRmoment :
      ∫⁻ ω, (ENNReal.ofReal (R ω)) ^ (128 : ℝ) ∂μ ≤
        ENNReal.ofReal ε ^ (128 : ℝ) := by
    have hmoment :
        ∫⁻ ω, (ENNReal.ofReal (R ω)) ^ (128 : ℝ) ∂μ =
          (eLpNorm R (128 : ℝ≥0) μ) ^ (128 : ℝ) := by
      rw [hRpow]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Real.enorm_of_nonneg (hR0 ω)]
    rw [hmoment]
    exact ENNReal.rpow_le_rpow hR128 (by norm_num)
  have hTpow :
      (eLpNorm T (2 : ℝ≥0) μ) ^ (2 : ℝ) =
        ∫⁻ ω, ‖T ω‖ₑ ^ (2 : ℝ) ∂μ := by
    exact eLpNorm_nnreal_pow_eq_lintegral (f := T) (p := (2 : ℝ≥0))
      (by norm_num) hTmeas
  have hTmoment :
      ∫⁻ ω, (ENNReal.ofReal (T ω)) ^ (2 : ℝ) ∂μ ≤
        ENNReal.ofReal C ^ (2 : ℝ) := by
    have hmoment :
        ∫⁻ ω, (ENNReal.ofReal (T ω)) ^ (2 : ℝ) ∂μ =
          (eLpNorm T (2 : ℝ≥0) μ) ^ (2 : ℝ) := by
      rw [hTpow]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Real.enorm_of_nonneg (hT0 ω)]
    rw [hmoment]
    exact ENNReal.rpow_le_rpow hT2 (by norm_num)
  have hprod (ω : Ω) :
      ∏ i ∈ S, F i ω ^ p i =
        (ENNReal.ofReal (R ω) ^ (128 : ℝ)) ^ ((n : ℝ) / 128) := by
    simp [S, F, p]
  have hTroot (ω : Ω) : G ω ^ (1 / 2 : ℝ) = ENNReal.ofReal (T ω) := by
    change (ENNReal.ofReal (T ω) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = _
    rw [← ENNReal.rpow_mul]
    norm_num
  have hRroot (ω : Ω) :
      (ENNReal.ofReal (R ω) ^ (128 : ℝ)) ^ ((n : ℝ) / 128) =
        (ENNReal.ofReal (R ω)) ^ n := by
    rw [← ENNReal.rpow_mul]
    have hexp : (128 : ℝ) * ((n : ℝ) / 128) = (n : ℝ) := by ring
    rw [hexp, ← ENNReal.rpow_natCast]
  have hleft (ω : Ω) :
      G ω ^ (1 / 2 : ℝ) * ∏ i ∈ S, F i ω ^ p i =
        (ENNReal.ofReal (R ω)) ^ n * ENNReal.ofReal (T ω) := by
    rw [hprod, hTroot, hRroot]
    exact mul_comm _ _
  have hholder' :
      ∫⁻ ω, G ω ^ (1 / 2 : ℝ) * ∏ i ∈ S, F i ω ^ p i ∂μ ≤
        (∫⁻ ω, G ω ∂μ) ^ (1 / 2 : ℝ) *
          ∏ i ∈ S, (∫⁻ ω, F i ω ∂μ) ^ p i := hholder
  rw [← lintegral_congr_ae (Filter.Eventually.of_forall hleft)]
  calc
    _ ≤ (∫⁻ ω, G ω ∂μ) ^ (1 / 2 : ℝ) *
        ∏ i ∈ S, (∫⁻ ω, F i ω ∂μ) ^ p i := hholder'
    _ ≤ (ENNReal.ofReal C ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        ((ENNReal.ofReal ε ^ (128 : ℝ)) ^ ((n : ℝ) / 128)) := by
      have hG : ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal C ^ (2 : ℝ) := by
        simpa [G] using hTmoment
      have hF0 : ∫⁻ ω, F 0 ω ∂μ ≤ ENNReal.ofReal ε ^ (128 : ℕ) := by
        change ∫⁻ ω, ENNReal.ofReal (R ω) ^ (128 : ℝ) ∂μ ≤
          ENNReal.ofReal ε ^ (128 : ℕ)
        calc
          _ ≤ ENNReal.ofReal ε ^ (128 : ℝ) := hRmoment
          _ = ENNReal.ofReal ε ^ (128 : ℕ) := ENNReal.rpow_natCast _ _
      have hF1 : ∫⁻ ω, F 1 ω ∂μ = 1 := by simp [F]
      have hprod' : ∏ i ∈ S, (∫⁻ ω, F i ω ∂μ) ^ p i ≤
          (ENNReal.ofReal ε ^ (128 : ℝ)) ^ ((n : ℝ) / 128) := by
        simp [S, p, hF1]
        gcongr
      exact mul_le_mul (ENNReal.rpow_le_rpow hG (by norm_num)) hprod'
        bot_le bot_le
    _ = ENNReal.ofReal (ε ^ n * C) := by
      have hrootC :
          (ENNReal.ofReal C ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ENNReal.ofReal C := by
        rw [← ENNReal.rpow_mul]
        norm_num
      have hrootε :
          (ENNReal.ofReal ε ^ (128 : ℝ)) ^ ((n : ℝ) / 128) =
            ENNReal.ofReal ε ^ n := by
        rw [← ENNReal.rpow_mul]
        have hexp : (128 : ℝ) * ((n : ℝ) / 128) = (n : ℝ) := by ring
        rw [hexp, ← ENNReal.rpow_natCast]
      rw [hrootC, hrootε]
      calc
        ENNReal.ofReal C * ENNReal.ofReal ε ^ n =
            ENNReal.ofReal (ε ^ n) * ENNReal.ofReal C := by
          rw [← ENNReal.ofReal_pow hε n]
          exact mul_comm _ _
        _ = ENNReal.ofReal (ε ^ n * C) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg hε n)]

/-- The mixed-bank monomial form used after expanding the global and OLD-local
positive splits. Four distinct `L¹²⁸` remainders can be correlated with the
same `L²` trace; the probability measure supplies the unused exponent. -/
theorem parent_gap_four_rare_trace_holder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Fin 4 → Ω → ℝ) (T : Ω → ℝ) (ε : Fin 4 → ℝ) (C : ℝ)
    (hR0 : ∀ i ω, 0 ≤ R i ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (hRmeas : ∀ i, AEStronglyMeasurable (R i) μ)
    (hTmeas : AEStronglyMeasurable T μ)
    (hR128 : ∀ i, eLpNorm (R i) 128 μ ≤ ENNReal.ofReal (ε i))
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    ∫⁻ ω, (∏ i : Fin 4, ENNReal.ofReal (R i ω)) * ENNReal.ofReal (T ω) ∂μ ≤
      ENNReal.ofReal C * ∏ i : Fin 4, ENNReal.ofReal (ε i) := by
  let S : Finset (Fin 4) := Finset.univ
  let F : Fin 4 → Ω → ℝ≥0∞ := fun i ω => ENNReal.ofReal (R i ω) ^ (8 : ℝ)
  let p : Fin 4 → ℝ := fun _ => 1 / 8
  let G : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (T ω) ^ (2 : ℝ)
  have hp_nonneg : ∀ i ∈ S, 0 ≤ p i := by intro i hi; simp [p]
  have hp_sum : (1 / 2 : ℝ) + ∑ i ∈ S, p i = 1 := by
    simp [S, p]
    norm_num
  have hFmeas : ∀ i ∈ S, AEMeasurable (F i) μ := by
    intro i hi
    change AEMeasurable (fun ω => ENNReal.ofReal (R i ω) ^ (8 : ℝ)) μ
    exact (ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (hRmeas i).aemeasurable).pow_const _
  have hGmeas : AEMeasurable G μ := by
    change AEMeasurable (fun ω => ENNReal.ofReal (T ω) ^ (2 : ℝ)) μ
    exact (ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      hTmeas.aemeasurable).pow_const _
  have hholder := ENNReal.lintegral_mul_prod_norm_pow_le
    (s := S) (g := G) (f := F) hGmeas hFmeas (1 / 2 : ℝ) (p := p)
    hp_sum (by norm_num) hp_nonneg
  have hR8 (i : Fin 4) : eLpNorm (R i) 8 μ ≤ ENNReal.ofReal (ε i) := by
    calc
      eLpNorm (R i) 8 μ ≤ eLpNorm (R i) 128 μ :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      _ ≤ ENNReal.ofReal (ε i) := hR128 i
  have hRmoment (i : Fin 4) :
      ∫⁻ ω, (ENNReal.ofReal (R i ω)) ^ (8 : ℝ) ∂μ ≤
        (ENNReal.ofReal (ε i)) ^ (8 : ℝ) := by
    have hpow : (eLpNorm (R i) (8 : ℝ≥0) μ) ^ (8 : ℝ) =
        ∫⁻ ω, ‖R i ω‖ₑ ^ (8 : ℝ) ∂μ := by
      exact eLpNorm_nnreal_pow_eq_lintegral (f := R i) (p := (8 : ℝ≥0))
        (by norm_num) (hRmeas i)
    have hmoment : ∫⁻ ω, (ENNReal.ofReal (R i ω)) ^ (8 : ℝ) ∂μ =
        (eLpNorm (R i) (8 : ℝ≥0) μ) ^ (8 : ℝ) := by
      rw [hpow]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Real.enorm_of_nonneg (hR0 i ω)]
    rw [hmoment]
    exact ENNReal.rpow_le_rpow (hR8 i) (by norm_num)
  have hTmoment :
      ∫⁻ ω, (ENNReal.ofReal (T ω)) ^ (2 : ℝ) ∂μ ≤
        (ENNReal.ofReal C) ^ (2 : ℝ) := by
    have hpow : (eLpNorm T (2 : ℝ≥0) μ) ^ (2 : ℝ) =
        ∫⁻ ω, ‖T ω‖ₑ ^ (2 : ℝ) ∂μ := by
      exact eLpNorm_nnreal_pow_eq_lintegral (f := T) (p := (2 : ℝ≥0))
        (by norm_num) hTmeas
    have hmoment : ∫⁻ ω, (ENNReal.ofReal (T ω)) ^ (2 : ℝ) ∂μ =
        (eLpNorm T (2 : ℝ≥0) μ) ^ (2 : ℝ) := by
      rw [hpow]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Real.enorm_of_nonneg (hT0 ω)]
    rw [hmoment]
    exact ENNReal.rpow_le_rpow hT2 (by norm_num)
  have hTroot (ω : Ω) : G ω ^ (1 / 2 : ℝ) = ENNReal.ofReal (T ω) := by
    change (ENNReal.ofReal (T ω) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = _
    rw [← ENNReal.rpow_mul]
    norm_num
  have hRroot (i : Fin 4) (ω : Ω) :
      F i ω ^ p i = ENNReal.ofReal (R i ω) := by
    change (ENNReal.ofReal (R i ω) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) = _
    rw [← ENNReal.rpow_mul]
    norm_num
  have hleft (ω : Ω) :
      G ω ^ (1 / 2 : ℝ) * ∏ i ∈ S, F i ω ^ p i =
        (∏ i : Fin 4, ENNReal.ofReal (R i ω)) * ENNReal.ofReal (T ω) := by
    rw [hTroot]
    change ENNReal.ofReal (T ω) *
      (∏ i : Fin 4, F i ω ^ p i) = _
    have hprod : ∏ i : Fin 4, F i ω ^ p i =
        ∏ i : Fin 4, ENNReal.ofReal (R i ω) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hRroot i ω
    rw [hprod]
    exact mul_comm _ _
  have hholder' :
      ∫⁻ ω, G ω ^ (1 / 2 : ℝ) * ∏ i ∈ S, F i ω ^ p i ∂μ ≤
        (∫⁻ ω, G ω ∂μ) ^ (1 / 2 : ℝ) *
          ∏ i ∈ S, (∫⁻ ω, F i ω ∂μ) ^ p i := hholder
  rw [← lintegral_congr_ae (Filter.Eventually.of_forall hleft)]
  calc
    _ ≤ (∫⁻ ω, G ω ∂μ) ^ (1 / 2 : ℝ) *
        ∏ i ∈ S, (∫⁻ ω, F i ω ∂μ) ^ p i := hholder'
    _ ≤ ((ENNReal.ofReal C) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        ∏ i : Fin 4, ((ENNReal.ofReal (ε i)) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) := by
      have hG : ∫⁻ ω, G ω ∂μ ≤ (ENNReal.ofReal C) ^ (2 : ℝ) := by
        simpa [G] using hTmoment
      have hF (i : Fin 4) : ∫⁻ ω, F i ω ∂μ ≤
          (ENNReal.ofReal (ε i)) ^ (8 : ℝ) := by
        simpa [F] using hRmoment i
      have hprod : ∏ i ∈ S, (∫⁻ ω, F i ω ∂μ) ^ p i ≤
          ∏ i : Fin 4, ((ENNReal.ofReal (ε i)) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) := by
        change ∏ i : Fin 4, (∫⁻ ω, F i ω ∂μ) ^ p i ≤ _
        apply Finset.prod_le_prod
        intro i hi
        exact ENNReal.rpow_le_rpow (hF i) (by norm_num)
      exact mul_le_mul (ENNReal.rpow_le_rpow hG (by norm_num)) hprod
        bot_le bot_le
    _ = ENNReal.ofReal C * ∏ i : Fin 4, ENNReal.ofReal (ε i) := by
      have hrootC : ((ENNReal.ofReal C) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
          ENNReal.ofReal C := by
        rw [← ENNReal.rpow_mul]
        norm_num
      have hrootε (i : Fin 4) :
          ((ENNReal.ofReal (ε i)) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) =
            ENNReal.ofReal (ε i) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      rw [hrootC]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact hrootε i

/-- One expanded mixed OLD/global term: the global history factor occurs at
most three times, one distinct OLD local remainder occurs once, and the raw
trace is in `L²`. The unused slots are the constant `1`. -/
theorem parent_gap_global_local_rare_term
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B R T : Ω → ℝ) (β ε C : ℝ) (k : ℕ) (hk : k ≤ 3)
    (hB0 : ∀ ω, 0 ≤ B ω) (hR0 : ∀ ω, 0 ≤ R ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (hBmeas : AEStronglyMeasurable B μ) (hRmeas : AEStronglyMeasurable R μ)
    (hTmeas : AEStronglyMeasurable T μ)
    (hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    ∫⁻ ω, (ENNReal.ofReal (B ω)) ^ k * ENNReal.ofReal (R ω) *
        ENNReal.ofReal (T ω) ∂μ ≤
      ENNReal.ofReal C * (ENNReal.ofReal β ^ k * ENNReal.ofReal ε) := by
  let P : Fin 4 → Ω → ℝ := fun i ω =>
    if i.val < k then B ω else if i.val = k then R ω else 1
  let E : Fin 4 → ℝ := fun i =>
    if i.val < k then β else if i.val = k then ε else 1
  have hconst : eLpNorm (fun _ : Ω => (1 : ℝ)) 128 μ = 1 := by
    rw [eLpNorm_const' (1 : ℝ) (by norm_num) (by norm_num),
      Real.enorm_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    norm_num
  have hP0 (i : Fin 4) (ω : Ω) : 0 ≤ P i ω := by
    by_cases hlt : i.val < k
    · simp [P, hlt, hB0 ω]
    · by_cases heq : i.val = k
      · simp [P, heq, hR0 ω]
      · simp [P, hlt, heq]
  have hPmeas (i : Fin 4) : AEStronglyMeasurable (P i) μ := by
    by_cases hlt : i.val < k
    · simpa [P, hlt] using hBmeas
    · by_cases heq : i.val = k
      · simpa [P, hlt, heq] using hRmeas
      · simpa [P, hlt, heq] using
          (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => (1 : ℝ)) μ)
  have hP128 (i : Fin 4) : eLpNorm (P i) 128 μ ≤ ENNReal.ofReal (E i) := by
    by_cases hlt : i.val < k
    · simpa [P, E, hlt] using hB128
    · by_cases heq : i.val = k
      · simpa [P, E, hlt, heq] using hR128
      · simpa [P, E, hlt, heq] using (le_of_eq hconst)
  have hholder := parent_gap_four_rare_trace_holder P T E C
    hP0 hT0 hPmeas hTmeas hP128 hT2
  have hleft (ω : Ω) :
      (∏ i : Fin 4, ENNReal.ofReal (P i ω)) * ENNReal.ofReal (T ω) =
        (ENNReal.ofReal (B ω)) ^ k * ENNReal.ofReal (R ω) *
          ENNReal.ofReal (T ω) := by
    have hprod : ∏ i : Fin 4, ENNReal.ofReal (P i ω) =
        ∏ i : Fin 4, (if i.val < k then ENNReal.ofReal (B ω)
          else if i.val = k then ENNReal.ofReal (R ω) else 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hlt : i.val < k
      · simp [P, hlt]
      · by_cases heq : i.val = k <;> simp [P, hlt, heq]
    rw [hprod, parent_gap_fin4_cutoff_product _ _ k hk]
  have hEprod : ∏ i : Fin 4, ENNReal.ofReal (E i) =
      ENNReal.ofReal β ^ k * ENNReal.ofReal ε := by
    calc
      _ = ∏ i : Fin 4, (if i.val < k then ENNReal.ofReal β
          else if i.val = k then ENNReal.ofReal ε else 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hlt : i.val < k
        · simp [E, hlt]
        · by_cases heq : i.val = k <;> simp [E, hlt, heq]
      _ = _ := parent_gap_fin4_cutoff_product _ _ k hk
  rw [← lintegral_congr_ae (Filter.Eventually.of_forall hleft)]
  calc
    _ ≤ ENNReal.ofReal C * ∏ i : Fin 4, ENNReal.ofReal (E i) := hholder
    _ = _ := by rw [hEprod]

end ASDExplicitGamma.Inverse
