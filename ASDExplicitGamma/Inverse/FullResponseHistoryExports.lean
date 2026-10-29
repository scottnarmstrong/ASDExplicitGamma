module

public import ASDExplicitGamma.Inverse.BankHistoryProfileArithmetic
public import ASDExplicitGamma.Inverse.PointwiseRoot
public import ASDExplicitGamma.Inverse.RootMeanInputs
public import ASDExplicitGamma.Inverse.FullResponseProfile

/-! The separate full inverse-history baseline and positive reserve of the source. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal
noncomputable section

/-- The complete-history remainder allowance fits the literal full-row e. -/
theorem full_response_history_allowance_le :
    bankRootHistoryRemainderAllowance (invFullRho:ℝ) ≤ (invFulle:ℝ) := by
  have ha : 0 ≤ (invE (11*invGamma):ℝ) := by norm_num [invE,invGamma]
  have hr : 0 ≤ (invFullRho:ℝ) := by
    exact_mod_cast (show (0:ℚ) ≤ invFullRho by decide +kernel)
  have hs : 0 ≤ (invSR:ℝ) := by
    exact_mod_cast (show (0:ℚ) ≤ invSR by decide +kernel)
  have hp : 1 ≤ (invPopulationRoot:ℝ) := by norm_num [invPopulationRoot]
  rw [bankRootHistoryRemainderAllowance,← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul (mul_nonneg ha hr),ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg ha hr) hs)]
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg ha hr) hs)
  convert hh using 1
  · ring
  · simp only [invFulle,Rat.cast_mul]
    ring

/-- The actual full complete inverse history has its source baseline and
separate positive reserve. The ENNReal history is explicitly finite almost
surely. All mean and pointwise-root inputs are discharged. -/
theorem full_response_history_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m J : ℤ)
    (hQ : Q.scale=m) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hpast : ∀ n < m, nativeInductionState M h n) :
    eLpNorm (fun ω => (bankRootInverseHistory Q M m J weights ω).toReal) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal ((invFullB0:ℝ)+(invFulle:ℝ)) ∧
    eLpNorm (fun ω => positiveSplitRemainder (bankRootInverseHistory Q M m J weights ω).toReal
      (invFullB0:ℝ) (1/2000)) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((invFulle:ℝ)^2/(4*(1/2000:ℝ))) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        bankRootInverseHistory Q M m J weights ω < ⊤) := by
  have hmean := clipped_inverse_mean_input_first_full M h hg m .full (Or.inr rfl) hpast
  have hA : 0 ≤ (invFullB0:ℝ) := by
    exact_mod_cast (show (0:ℚ) ≤ invFullB0 by decide +kernel)
  have he : 0 ≤ (invFulle:ℝ) := ENNReal.toReal_nonneg.trans full_response_history_allowance_le
  have hb := bank_full_root_inverse_baseline_history_cap M Q m hQ hg
  have hr := bank_full_root_inverse_remainder_history_L256_cap_of_pointwise
    M h hM hg Q m J hQ hmJ weights hw hpast hmean (q3_pointwise_root M h hM hg)
  rw [← bankRootHistoryRemainderAllowance_ofReal] at hr
  have hr' := hr.trans (ENNReal.ofReal_le_ofReal full_response_history_allowance_le)
  have hh := bank_root_inverse_history_L128_split_of_caps M h hM hg Q m J hQ.le hmJ weights hw
    .full hpast hmean (q3_pointwise_root M h hM hg) (invFullB0:ℝ) (1/2000) (invFulle:ℝ)
    hA (by norm_num) he hb hr'
  constructor
  · exact hh.1.trans_eq (ENNReal.ofReal_add hA he).symm
  · constructor
    · apply hh.2.trans_eq
      rw [← ENNReal.ofReal_pow he,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/(4*(1/2000)))]
      congr 1
      ring
    · let μ := (Cutoff.cutoffSampleLaw M).toMeasure
      let R := bankRootInverseRemainderHistory Q M m .full
      have hR : Measurable R := bank_root_inverse_remainder_history_measurable
        M h hM hg Q m J hQ.le hmJ weights hw .full hpast hmean (q3_pointwise_root M h hM hg)
      have hpow : (∫⁻ ω, (R ω)^256 ∂μ) ≠ ⊤ := by
        rw [← bank_L256_power μ R hR]
        exact ne_top_of_le_ne_top (by simp) (pow_le_pow_left' hr' 256)
      have hRpow : ∀ᵐ ω ∂μ, (R ω)^256 < ⊤ := ae_lt_top (hR.pow_const 256) hpow
      have hRfinite : ∀ᵐ ω ∂μ, R ω < ⊤ := hRpow.mono fun ω hω => by
        by_contra htop
        have htop' : R ω = ⊤ := by simpa using htop
        simp only [htop',ENNReal.top_pow (by norm_num : (256:ℕ) ≠ 0),lt_self_iff_false] at hω
      have hsplit := bank_root_inverse_history_split_of_pointwise M h Q m J hQ.le hmJ
        weights hw .full hpast hmean (q3_pointwise_root M h hM hg)
      filter_upwards [hsplit,hRfinite] with ω hω hRω
      exact (hω.trans (add_le_add hb le_rfl)).trans_lt
        (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,hRω⟩)

/-- The separate complete-history baseline-plus-error and positive reserve
have the exact certified outward bounds stated in the source. -/
theorem full_response_history_numerical_caps :
    (invFullB0:ℝ)+(invFulle:ℝ) < 2.031006 ∧
      (invFulle:ℝ)^2/(4*(1/2000:ℝ)) < 1/10^34 := by
  have hh := bank_full_response_positive_history_bound
  norm_num only [Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat] at hh
  norm_num at hh ⊢
  exact hh

/-- The p=64 dimension-two complete-history factors exported for both rows,
with the positive geometric denominator retained explicitly. -/
theorem full_response_history_factor_caps :
    (0:ℝ) < 1-(invHistoryRoot:ℝ)*(invE (22/5*invGamma):ℝ) ∧
      (invSi:ℝ) < 1.12734 ∧ (invS0:ℝ) < 1.130469 ∧ (invS1:ℝ) < 4.190715 := by
  refine ⟨?_,?_,?_,?_⟩
  · have hh : (0:ℝ) < ((1-invHistoryRoot*invE (22/5*invGamma):ℚ):ℝ) := by
      exact_mod_cast invFullHistory_caps.1
    simpa only [Rat.cast_sub,Rat.cast_one,Rat.cast_mul] using hh
  · have hh : (invSi:ℝ) < ((1.12734:ℚ):ℝ) := by exact_mod_cast invFullHistory_caps.2.1
    norm_num at hh ⊢
    exact hh
  · have hh : (invS0:ℝ) < ((1.130469:ℚ):ℝ) := by exact_mod_cast invFullHistory_caps.2.2.1
    norm_num at hh ⊢
    exact hh
  · have hh : (invS1:ℝ) < ((4.190715:ℚ):ℝ) := by exact_mod_cast invFullHistory_caps.2.2.2
    norm_num at hh ⊢
    exact hh

end
end ASDExplicitGamma.Inverse
