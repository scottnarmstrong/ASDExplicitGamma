module

public import ASDExplicitGamma.Native.HeatVHEATError
public import ASDExplicitGamma.Native.HeatVHEATBounds
public import ASDExplicitGamma.Native.HeatVHEATFamily
public import ASDExplicitGamma.Native.GenericSourceInterpolation
public import ASDExplicitGamma.Native.GenericSourceMeanHolder
public import ASDExplicitGamma.Gaussian.GaussMomentHolder

/-! The exact generalized-Hölder envelope used by the full-polynomial VHEAT
error, including its exceptional top-degree interpolation. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ASDExplicitGamma.Gaussian
open scoped ENNReal

private theorem memLp_of_eLpNormPrime_le_ofReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {q C : ℝ} (hq : 0 < q)
    (hcap : eLpNorm' f q μ ≤ ENNReal.ofReal C) :
    MemLp f (ENNReal.ofReal q) μ := by
  have heq : eLpNorm f (ENNReal.ofReal q) μ = eLpNorm' f q μ := by
    simpa only [ENNReal.toReal_ofReal hq.le] using
      (eLpNorm_eq_eLpNorm' (p := ENNReal.ofReal q)
        (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top hf)
  apply memLp_iff.mpr
  rw [heq]
  exact hcap.trans_lt ENNReal.ofReal_lt_top

private theorem holder_power_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Ω → ℝ) (p q : ℝ)
    (hconj : p.HolderConjugate q)
    (hAsm : AEStronglyMeasurable A μ) (hBsm : AEStronglyMeasurable B μ)
    (hA0 : ∀ ω, 0 ≤ A ω) (hB0 : ∀ ω, 0 ≤ B ω)
    (hAmem : MemLp A (ENNReal.ofReal p) μ)
    (hBmem : MemLp B (ENNReal.ofReal q) μ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAcap : eLpNorm' A p μ ≤ ENNReal.ofReal a)
    (hBcap : eLpNorm' B q μ ≤ ENNReal.ofReal b) :
    Integrable (fun ω => A ω * B ω) μ ∧
      (∫ ω, A ω * B ω ∂μ) ≤ a * b := by
  have hp : 0 < p := hconj.pos
  have hq : 0 < q := hconj.symm.pos
  have holderTriple : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 :=
    hconj.ennrealOfReal
  have hApos := native_source_positive_norm_le_prime_cap
    μ A hAsm hA0 p a hp ha hAcap
  have hBpos := native_source_positive_norm_le_prime_cap
    μ B hBsm hB0 q b hq hb hBcap
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Filter.Eventually.of_forall hA0) (Filter.Eventually.of_forall hB0)
    hAmem hBmem
  have hholder' :
      (∫ ω, A ω * B ω ∂μ) ≤
        positiveLpNorm μ p A * positiveLpNorm μ q B := by
    simpa only [positiveLpNorm, one_div] using hholder
  have hproductMem : MemLp (A * B) 1 μ :=
    @MemLp.mul Ω inferInstance ℝ inferInstance μ
      (ENNReal.ofReal p) (ENNReal.ofReal q) 1 B A hAmem hBmem holderTriple
  refine ⟨memLp_one_iff_integrable.mp hproductMem, ?_⟩
  have hBnorm0 : 0 ≤ positiveLpNorm μ q B := by
    unfold positiveLpNorm
    exact Real.rpow_nonneg
      (integral_nonneg fun ω => Real.rpow_nonneg (hB0 ω) q) _
  exact hholder'.trans (mul_le_mul hApos hBpos hBnorm0 ha)

/-- The OLD order-128 remainder factor and the actual heat trace obey the
sub-top VHEAT Hölder envelope. -/
theorem nativeHeatVHEATJ_integral_holder_of_lt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R T : Ω → ℝ)
    (hRsm : AEStronglyMeasurable R μ) (hTsm : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω, 0 ≤ R ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (p j l : ℕ) (hp1 : 1 ≤ p) (hp20 : p ≤ 20)
    (hj1 : 1 ≤ j) (hj2 : j ≤ 2) (hlp : l < p)
    (ε X : ℝ) (hε : 0 ≤ ε) (hX : 0 < X)
    (hRcap : eLpNorm' R 128 μ ≤ ENNReal.ofReal ε)
    (hTcap : eLpNorm' T p μ ≤ ENNReal.ofReal X) :
    Integrable (fun ω => R ω ^ j * T ω ^ l) μ ∧
      (∫ ω, R ω ^ j * T ω ^ l ∂μ) ≤ nativeHeatVHEATJ ε X 0 p j l := by
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp1
  have hjR : 0 < (j : ℝ) := by positivity
  have hpowR :
      eLpNorm' (fun ω => R ω ^ j) (128 / (j : ℝ)) μ ≤
        ENNReal.ofReal (ε ^ j) := by
    have hnorm :
        eLpNorm' (fun ω => ‖R ω‖ ^ (j : ℝ)) (128 / (j : ℝ)) μ =
          eLpNorm' R 128 μ ^ (j : ℝ) := by
      rw [eLpNorm'_norm_rpow R (128 / (j : ℝ)) (j : ℝ) hjR]
      congr 1
      field_simp
    have hfun : (fun ω => ‖R ω‖ ^ (j : ℝ)) = fun ω => R ω ^ j := by
      funext ω
      rw [Real.norm_of_nonneg (hR0 ω), Real.rpow_natCast]
    rw [← hfun, hnorm]
    calc
      eLpNorm' R 128 μ ^ (j : ℝ) ≤
          ENNReal.ofReal ε ^ (j : ℝ) :=
            ENNReal.rpow_le_rpow hRcap (by positivity)
      _ = ENNReal.ofReal (ε ^ j) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hε (by positivity)]
        rw [Real.rpow_natCast]
  have hRpowSm : AEStronglyMeasurable (fun ω => R ω ^ j) μ := hRsm.pow j
  have hRpow0 (ω : Ω) : 0 ≤ R ω ^ j := pow_nonneg (hR0 ω) _
  have hRpowMem := memLp_of_eLpNormPrime_le_ofReal hRpowSm
    (by positivity : 0 < 128 / (j : ℝ)) hpowR
  by_cases hl0 : l = 0
  · subst l
    have hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε := by
      have heq : eLpNorm R 128 μ = eLpNorm' R 128 μ := by
        simpa using (eLpNorm_eq_eLpNorm' (p := (128 : ℝ≥0∞))
          (by norm_num) (by norm_num) hRsm)
      rw [heq]
      exact hRcap
    have hmoment := nativeHeat_integral_natPow_le_of_eLpNorm128
      (μ := μ) inferInstance hRsm hR0 ε hε hR128 j hj1 (by omega)
    have hEq : (fun ω => R ω ^ j * T ω ^ 0) = fun ω => R ω ^ j := by
      funext ω
      simp
    rw [hEq]
    refine ⟨?_, ?_⟩
    · apply hRpowMem.integrable
      have hjRle : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
      have hq : (1 : ℝ) ≤ 128 / (j : ℝ) := by
        rw [le_div_iff₀ hjR]
        norm_num
        linarith
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq
    · rw [nativeHeatVHEATJ_of_lt ε X 0 p j 0 (by omega)]
      simpa using hmoment
  · have hl1 : 1 ≤ l := by omega
    let qA : ℝ := 128 / (j : ℝ)
    let qB : ℝ := 128 / (128 - (j : ℝ))
    let rT : ℝ := (p : ℝ) / (l : ℝ)
    have hjRle : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
    have hdenPos : 0 < 128 - (j : ℝ) := by linarith
    have hqApos : 0 < qA := by dsimp [qA]; positivity
    have hqBpos : 0 < qB := by dsimp [qB]; exact div_pos (by norm_num) hdenPos
    have hqBgt : 1 < qB := by
      dsimp [qB]
      rw [one_lt_div hdenPos]
      have hjlt : (j : ℝ) < 128 := by exact_mod_cast (by omega : j < 128)
      linarith
    have hconj : qA.HolderConjugate qB := by
      have hconj' : (qB / (qB - 1)).HolderConjugate qB :=
        (Real.holderConjugate_iff_eq_conjExponent hqBgt).mpr rfl |>.symm
      have hsub : qB - 1 = (j : ℝ) / (128 - (j : ℝ)) := by
        dsimp [qB]
        field_simp
        ring
      have heq : qB / (qB - 1) = qA := by
        rw [hsub]
        dsimp [qA, qB]
        field_simp
      rw [heq] at hconj'
      exact hconj'
    have hqB_le_rT : qB ≤ rT := by
      dsimp [qB, rT]
      have hp20R : (p : ℝ) ≤ 20 := by exact_mod_cast hp20
      have hlpR : (l : ℝ) ≤ (p : ℝ) - 1 := by
        exact_mod_cast (by omega : l ≤ p - 1)
      have hpj : (p : ℝ) * (j : ℝ) ≤ 40 := by
        calc
          (p : ℝ) * (j : ℝ) ≤ (p : ℝ) * 2 :=
            mul_le_mul_of_nonneg_left hjRle (by positivity)
          _ ≤ 20 * 2 := mul_le_mul_of_nonneg_right hp20R (by norm_num)
          _ = 40 := by norm_num
      have hnum :
          0 ≤ (p : ℝ) * (128 - (j : ℝ)) - 128 * (l : ℝ) := by
        have hlterm : 128 * (l : ℝ) ≤ 128 * ((p : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hlpR (by norm_num)
        nlinarith [hpj, hlterm]
      exact (div_le_div_iff₀ hdenPos
        (by positivity : 0 < (l : ℝ))).mpr (by nlinarith)
    have hTpowCap : eLpNorm' (fun ω => T ω ^ l) rT μ ≤
        ENNReal.ofReal (X ^ l) := by
      have hnorm :
          eLpNorm' (fun ω => ‖T ω‖ ^ (l : ℝ)) rT μ =
            eLpNorm' T (p : ℝ) μ ^ (l : ℝ) := by
        rw [eLpNorm'_norm_rpow T rT (l : ℝ) (by positivity)]
        congr 1
        dsimp [rT]
        field_simp
      have hfun : (fun ω => ‖T ω‖ ^ (l : ℝ)) = fun ω => T ω ^ l := by
        funext ω
        rw [Real.norm_of_nonneg (hT0 ω), Real.rpow_natCast]
      rw [← hfun, hnorm]
      calc
        eLpNorm' T (p : ℝ) μ ^ (l : ℝ) ≤
            ENNReal.ofReal X ^ (l : ℝ) :=
              ENNReal.rpow_le_rpow hTcap (by positivity)
        _ = ENNReal.ofReal (X ^ l) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hX.le (by positivity)]
          rw [Real.rpow_natCast]
    have hTpowLow : eLpNorm' (fun ω => T ω ^ l) qB μ ≤
        ENNReal.ofReal (X ^ l) := by
      exact (eLpNorm'_le_eLpNorm'_of_exponent_le hqBpos hqB_le_rT μ
        (hTsm.pow l)).trans hTpowCap
    have hTpowSm : AEStronglyMeasurable (fun ω => T ω ^ l) μ := hTsm.pow l
    have hTpowMem := memLp_of_eLpNormPrime_le_ofReal hTpowSm hqBpos
      hTpowLow
    have hProduct := holder_power_integral_le μ
      (fun ω => R ω ^ j) (fun ω => T ω ^ l) qA qB hconj
      hRpowSm (hTsm.pow l) hRpow0 (fun ω => pow_nonneg (hT0 ω) l)
      hRpowMem hTpowMem (ε ^ j) (X ^ l)
      (pow_nonneg hε j) (pow_nonneg hX.le l) hpowR hTpowLow
    have hIntegral : Integrable (fun ω => R ω ^ j * T ω ^ l) μ := hProduct.1
    have hle :
        (∫ ω, R ω ^ j * T ω ^ l ∂μ) ≤ ε ^ j * X ^ l := by
      exact hProduct.2
    rw [nativeHeatVHEATJ_of_lt ε X 0 p j l hlp]
    exact ⟨hIntegral, hle⟩

end ASDExplicitGamma.Native

end
