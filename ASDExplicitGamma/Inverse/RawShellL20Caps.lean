module

public import ASDExplicitGamma.Inverse.RawShellBankCaps
public import ASDExplicitGamma.Gaussian.GaussMomentHolder

/-! The order-128 bank caps imply the actual-law L20 factors used by the
p=20 moment chain. Products use the measurable bank majorant `P`;
the source histories only need to be dominated by it almost everywhere. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Filter MeasureTheory
open ASDExplicitGamma.Gaussian
open scoped ENNReal

/-- Lower local-inverse and full-response order-128 caps to actual-law L20
quantities, allowing a caller-supplied full-response cap. -/
theorem raw_trace_p20_bank_holder_caps_of_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P F T D : Ω → ℝ) (fCap : ℝ) (hfCap : 0 ≤ fCap)
    (hP0 : ∀ ω, 0 ≤ P ω) (hF0 : ∀ ω, 0 ≤ F ω)
    (hT0 : ∀ ω, 0 ≤ T ω) (hD0 : ∀ ω, 0 ≤ D ω)
    (hTF : ∀ᵐ ω ∂μ, T ω ≤ F ω)
    (hD : ∀ᵐ ω ∂μ, D ω ≤ 2 * P ω)
    (hPmeas : AEStronglyMeasurable P μ) (hFmeas : AEStronglyMeasurable F μ)
    (hTmeas : AEStronglyMeasurable T μ) (hDmeas : AEStronglyMeasurable D μ)
    (hP128 : eLpNorm P (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal (3683 / 2500 : ℝ))
    (hF128 : eLpNorm F (128 : ℝ≥0∞) μ ≤
      ENNReal.ofReal fCap) :
    MemLp T (ENNReal.ofReal 20) μ ∧
    MemLp D (ENNReal.ofReal 20) μ ∧
    MemLp (fun ω => P ω * F ω) (ENNReal.ofReal 20) μ ∧
    MemLp (fun ω => P ω ^ 2 * F ω) (ENNReal.ofReal 20) μ ∧
    positiveLpNorm μ 20 T ≤ fCap ∧
    positiveLpNorm μ 20 D ≤ 2 * (3683 / 2500 : ℝ) ∧
    positiveLpNorm μ 20 (fun ω => P ω * F ω) ≤
      (3683 / 2500 : ℝ) * fCap ∧
    positiveLpNorm μ 20 (fun ω => P ω ^ 2 * F ω) ≤
      (3683 / 2500 : ℝ) ^ 2 * fCap := by
  have hb : 0 ≤ (3683 / 2500 : ℝ) := by positivity
  have hf : 0 ≤ fCap := hfCap
  have hP60 := raw_trace_local_inverse_L60_of_L128 μ P hPmeas hP128
  have hP60' : eLpNorm P (ENNReal.ofReal 60) μ ≤ ENNReal.ofReal (3683 / 2500 : ℝ) := by
    simpa using hP60
  have hF60' : eLpNorm F (ENNReal.ofReal 60) μ ≤
      ENNReal.ofReal fCap := by
    have hF20raw := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := F) (μ := μ)
      (show (ENNReal.ofReal 60) ≤ (128 : ℝ≥0∞) by norm_num) hFmeas
    have hmono : eLpNorm F (ENNReal.ofReal 60) μ ≤ eLpNorm F 128 μ := by
      simpa only [measure_univ, ENNReal.one_rpow, mul_one] using hF20raw
    exact hmono.trans hF128
  have hP20raw := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := P) (μ := μ)
    (show (ENNReal.ofReal 20) ≤ (128 : ℝ≥0∞) by norm_num) hPmeas
  have hP20 : eLpNorm P (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal (3683 / 2500 : ℝ) := by
    have hmono : eLpNorm P (ENNReal.ofReal 20) μ ≤ eLpNorm P 128 μ := by
      simpa only [measure_univ, ENNReal.one_rpow, mul_one] using hP20raw
    exact hmono.trans hP128
  have hF20raw := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := F) (μ := μ)
    (show (ENNReal.ofReal 20) ≤ (128 : ℝ≥0∞) by norm_num) hFmeas
  have hF20 : eLpNorm F (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal fCap := by
    have hmono : eLpNorm F (ENNReal.ofReal 20) μ ≤ eLpNorm F 128 μ := by
      simpa only [measure_univ, ENNReal.one_rpow, mul_one] using hF20raw
    exact hmono.trans hF128
  have hTFnorm : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ ‖F ω‖ := hTF.mono fun ω hω => by
    rw [Real.norm_of_nonneg (hT0 ω), Real.norm_of_nonneg (hF0 ω)]
    exact hω
  have hT20 : eLpNorm T (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal fCap := by
    exact (eLpNorm_mono_ae hTmeas hTFnorm).trans hF20
  have hDnorm : ∀ᵐ ω ∂μ, ‖D ω‖ ≤ ‖2 * P ω‖ := hD.mono fun ω hω => by
    rw [Real.norm_of_nonneg (hD0 ω),
      Real.norm_of_nonneg (mul_nonneg (by norm_num) (hP0 ω))]
    exact hω
  have hD20 : eLpNorm D (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal (2 * (3683 / 2500 : ℝ)) := by
    have hDmono : eLpNorm D (ENNReal.ofReal 20) μ ≤
        eLpNorm (fun ω => 2 * P ω) (ENNReal.ofReal 20) μ :=
      eLpNorm_mono_ae hDmeas hDnorm
    have hsmul : (fun ω => 2 * P ω) = (2 : ℝ) • P := by
      ext ω
      simp
    calc
      _ ≤ eLpNorm (fun ω => 2 * P ω) (ENNReal.ofReal 20) μ := hDmono
      _ = ENNReal.ofReal 2 * eLpNorm P (ENNReal.ofReal 20) μ := by
        rw [hsmul, eLpNorm_const_smul]
        simp [Real.enorm_eq_ofReal]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (3683 / 2500 : ℝ) := by
        gcongr
      _ = ENNReal.ofReal (2 * (3683 / 2500 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
  have hPFsm : AEStronglyMeasurable (fun ω => P ω * F ω) μ := hPmeas.mul hFmeas
  have hP2sm : AEStronglyMeasurable (fun ω => P ω ^ 2) μ := by
    have heq : (fun ω => P ω ^ 2) = P * P := by
      funext ω
      simp [pow_two]
    rw [heq]
    exact hPmeas.mul hPmeas
  have h606030 : Real.HolderTriple 60 60 30 := by
    constructor <;> norm_num
  have h306020 : Real.HolderTriple 30 60 20 := by
    constructor <;> norm_num
  have hPF30 : eLpNorm (fun ω => P ω * F ω) (ENNReal.ofReal 30) μ ≤
      ENNReal.ofReal ((3683 / 2500 : ℝ) * fCap) := by
    letI : ENNReal.HolderTriple (ENNReal.ofReal 60) (ENNReal.ofReal 60)
        (ENNReal.ofReal 30) := h606030.ennrealOfReal
    have hholder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := ENNReal.ofReal 60) (q := ENNReal.ofReal 60) (r := ENNReal.ofReal 30)
      (fun x y : ℝ => x * y) 1 continuous_mul hPmeas hFmeas
      (Eventually.of_forall fun ω => by simp [norm_mul])
    calc
      _ ≤ eLpNorm P (ENNReal.ofReal 60) μ * eLpNorm F (ENNReal.ofReal 60) μ := by
        simpa using hholder
      _ ≤ ENNReal.ofReal (3683 / 2500 : ℝ) *
          ENNReal.ofReal fCap := by
        gcongr
      _ = ENNReal.ofReal ((3683 / 2500 : ℝ) * fCap) := by
        rw [← ENNReal.ofReal_mul hb]
  have hP2_30 : eLpNorm (fun ω => P ω ^ 2) (ENNReal.ofReal 30) μ ≤
      ENNReal.ofReal ((3683 / 2500 : ℝ) ^ 2) := by
    letI : ENNReal.HolderTriple (ENNReal.ofReal 60) (ENNReal.ofReal 60)
        (ENNReal.ofReal 30) := h606030.ennrealOfReal
    have hholder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := ENNReal.ofReal 60) (q := ENNReal.ofReal 60) (r := ENNReal.ofReal 30)
      (fun x y : ℝ => x * y) 1 continuous_mul hPmeas hPmeas
      (Eventually.of_forall fun ω => by simp [norm_mul])
    calc
      _ ≤ eLpNorm P (ENNReal.ofReal 60) μ * eLpNorm P (ENNReal.ofReal 60) μ := by
        simpa [pow_two] using hholder
      _ ≤ ENNReal.ofReal (3683 / 2500 : ℝ) * ENNReal.ofReal (3683 / 2500 : ℝ) := by
        gcongr
      _ = ENNReal.ofReal ((3683 / 2500 : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul hb]
        congr 1
        ring
  have hP2mem : MemLp (fun ω => P ω ^ 2) (ENNReal.ofReal 30) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hP2_30 ENNReal.ofReal_lt_top
  have hP2F20 : eLpNorm (fun ω => P ω ^ 2 * F ω) (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal ((3683 / 2500 : ℝ) ^ 2 * fCap) := by
    letI : ENNReal.HolderTriple (ENNReal.ofReal 30) (ENNReal.ofReal 60)
        (ENNReal.ofReal 20) := h306020.ennrealOfReal
    have hholder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := ENNReal.ofReal 30) (q := ENNReal.ofReal 60) (r := ENNReal.ofReal 20)
      (fun x y : ℝ => x * y) 1 continuous_mul hP2sm hFmeas
      (Eventually.of_forall fun ω => by simp [norm_mul])
    calc
      _ ≤ eLpNorm (fun ω => P ω ^ 2) (ENNReal.ofReal 30) μ *
            eLpNorm F (ENNReal.ofReal 60) μ := by
        simpa using hholder
      _ ≤ ENNReal.ofReal ((3683 / 2500 : ℝ) ^ 2) *
          ENNReal.ofReal fCap := by
        gcongr
      _ = ENNReal.ofReal ((3683 / 2500 : ℝ) ^ 2 * fCap) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg (3683 / 2500 : ℝ))]
  have hPF20raw := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := fun ω => P ω * F ω) (μ := μ)
    (show (ENNReal.ofReal 20) ≤ ENNReal.ofReal 30 by norm_num) hPFsm
  have hPF20 : eLpNorm (fun ω => P ω * F ω) (ENNReal.ofReal 20) μ ≤
      ENNReal.ofReal ((3683 / 2500 : ℝ) * fCap) := by
    have hmono : eLpNorm (fun ω => P ω * F ω) (ENNReal.ofReal 20) μ ≤
        eLpNorm (fun ω => P ω * F ω) (ENNReal.ofReal 30) μ := by
      simpa only [measure_univ, ENNReal.one_rpow, mul_one] using hPF20raw
    exact hmono.trans hPF30
  have hTmem : MemLp T (ENNReal.ofReal 20) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hT20 ENNReal.ofReal_lt_top
  have hDmem : MemLp D (ENNReal.ofReal 20) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hD20 ENNReal.ofReal_lt_top
  have hPFmem : MemLp (fun ω => P ω * F ω) (ENNReal.ofReal 20) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hPF20 ENNReal.ofReal_lt_top
  have hP2Fmem : MemLp (fun ω => P ω ^ 2 * F ω) (ENNReal.ofReal 20) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hP2F20 ENNReal.ofReal_lt_top
  have hTpos : positiveLpNorm μ 20 T ≤ fCap := by
    rw [positiveLpNorm_eq_eLpNorm_toReal μ (by norm_num) T hT0 hTmem]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hT20).trans_eq
      (ENNReal.toReal_ofReal hf)
  have hDpos : positiveLpNorm μ 20 D ≤ 2 * (3683 / 2500 : ℝ) := by
    rw [positiveLpNorm_eq_eLpNorm_toReal μ (by norm_num) D hD0 hDmem]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hD20).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hb))
  have hPFpos : positiveLpNorm μ 20 (fun ω => P ω * F ω) ≤
      (3683 / 2500 : ℝ) * fCap := by
    rw [positiveLpNorm_eq_eLpNorm_toReal μ (by norm_num)
      (fun ω => P ω * F ω) (fun ω => mul_nonneg (hP0 ω) (hF0 ω)) hPFmem]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hPF20).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hb hf))
  have hP2Fpos : positiveLpNorm μ 20 (fun ω => P ω ^ 2 * F ω) ≤
      (3683 / 2500 : ℝ) ^ 2 * fCap := by
    rw [positiveLpNorm_eq_eLpNorm_toReal μ (by norm_num)
      (fun ω => P ω ^ 2 * F ω)
      (fun ω => mul_nonneg (sq_nonneg (P ω)) (hF0 ω)) hP2Fmem]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hP2F20).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hf))
  exact ⟨hTmem, hDmem, hPFmem, hP2Fmem, hTpos, hDpos, hPFpos, hP2Fpos⟩

/-- Lower the standard local-inverse and full-response order-128 bank caps
to the actual-law L20 quantities. -/
theorem raw_trace_p20_bank_holder_caps
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P F T D : Ω → ℝ) (gamma : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma)
    (hP0 : ∀ ω, 0 ≤ P ω) (hF0 : ∀ ω, 0 ≤ F ω)
    (hT0 : ∀ ω, 0 ≤ T ω) (hD0 : ∀ ω, 0 ≤ D ω)
    (hTF : ∀ᵐ ω ∂μ, T ω ≤ F ω)
    (hD : ∀ᵐ ω ∂μ, D ω ≤ 2 * P ω)
    (hPmeas : AEStronglyMeasurable P μ) (hFmeas : AEStronglyMeasurable F μ)
    (hTmeas : AEStronglyMeasurable T μ) (hDmeas : AEStronglyMeasurable D μ)
    (hP128 : eLpNorm P (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal (3683 / 2500 : ℝ))
    (hF128 : eLpNorm F (128 : ℝ≥0∞) μ ≤
      ENNReal.ofReal (rawTraceFullResponseCap gamma h)) :
    MemLp T (ENNReal.ofReal 20) μ ∧
    MemLp D (ENNReal.ofReal 20) μ ∧
    MemLp (fun ω => P ω * F ω) (ENNReal.ofReal 20) μ ∧
    MemLp (fun ω => P ω ^ 2 * F ω) (ENNReal.ofReal 20) μ ∧
    positiveLpNorm μ 20 T ≤ rawTraceFullResponseCap gamma h ∧
    positiveLpNorm μ 20 D ≤ 2 * (3683 / 2500 : ℝ) ∧
    positiveLpNorm μ 20 (fun ω => P ω * F ω) ≤
      (3683 / 2500 : ℝ) * rawTraceFullResponseCap gamma h ∧
    positiveLpNorm μ 20 (fun ω => P ω ^ 2 * F ω) ≤
      (3683 / 2500 : ℝ) ^ 2 * rawTraceFullResponseCap gamma h := by
  have hfCap : 0 ≤ rawTraceFullResponseCap gamma h := by
    unfold rawTraceFullResponseCap
    positivity
  exact raw_trace_p20_bank_holder_caps_of_cap μ P F T D
    (rawTraceFullResponseCap gamma h) hfCap hP0 hF0 hT0 hD0 hTF hD
    hPmeas hFmeas hTmeas hDmeas hP128 hF128

end ASDExplicitGamma.Inverse
