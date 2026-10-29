module

public import ASDExplicitGamma.Native.HeatVHEATDriftRareIntegral
public import ASDExplicitGamma.Native.HeatVHEATHolder

/-! The zero actual heat-norm endpoint, needed before using intrinsic norms
as X. This does not replace or reprove the existing Holder estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Pure rare moments are the zero-trace-degree case of the proved J
payment, including genuine integrability. -/
theorem heatVHEATDrift_rare_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hR0 : ∀ ω,0 ≤ R ω)
    (eps : ℝ) (heps : 0 ≤ eps) (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal eps)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    Integrable (fun ω => R ω^j) μ ∧ (∫ ω,R ω^j ∂μ) ≤ eps^j := by
  have hr : eLpNorm' R 128 μ ≤ ENNReal.ofReal eps := by
    simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0) (by norm_num) hR,
      ENNReal.toReal_ofNat] using hR128
  have ht : eLpNorm' (fun _ : Ω => (0:ℝ)) 20 μ ≤ ENNReal.ofReal (1:ℝ) := by
    change eLpNorm' (0 : Ω → ℝ) 20 μ ≤ _
    rw [eLpNorm'_zero (by norm_num : (0:ℝ)<20)]
    exact bot_le
  have hh := nativeHeatVHEATJ_integral_holder_of_lt μ R (fun _ => 0) hR
    aestronglyMeasurable_zero hR0 (fun _ => le_rfl) 20 j 0 (by norm_num) le_rfl hj1 hj2
    (by norm_num) eps 1 heps (by norm_num) hr ht
  simpa only [pow_zero,mul_one,nativeHeatVHEATJ_of_lt eps 1 0 20 j 0 (by norm_num)] using hh

/-- First-line payments are nonnegative also when the actual X norm is zero. -/
theorem heatVHEATDrift_first_line_nonneg
    (k : ℕ) (e K C b eps X F : ℝ) (he : 0 ≤ e) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hb : 0 ≤ b) (heps : 0 ≤ eps) (hX : 0 ≤ X) (hF : 0 ≤ F) :
    0 ≤ heatVHEATDriftFirstLine k e K C b eps X F := by
  have hJ (j l : ℕ) : 0 ≤ nativeHeatVHEATJ eps X F 20 j l := by
    unfold nativeHeatVHEATJ
    split_ifs
    · exact mul_nonneg (pow_nonneg heps _) (pow_nonneg hX _)
    · exact mul_nonneg (mul_nonneg (pow_nonneg heps _) (pow_nonneg hX _))
        (Real.rpow_nonneg (div_nonneg hF hX) _)
  unfold heatVHEATDriftFirstLine
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) he)
    (add_nonneg (mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (mul_nonneg (by norm_num) hb) hC))
      (add_nonneg (mul_nonneg (by norm_num) (hJ _ _)) (hJ _ _)))
      (mul_nonneg hC (add_nonneg (mul_nonneg (by norm_num) (hJ _ _)) (hJ _ _))))

/-- The complete rare first line is valid at zero actual heat norm. The
k=1 predecessor term is kept: only the trace, not T+4, vanishes. -/
theorem heatVHEATDrift_rare_zero_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R A T : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hR0 : ∀ ω,0 ≤ R ω)
    (hAzero : A =ᵐ[μ] 0) (hTzero : T =ᵐ[μ] 0)
    (k : ℕ) (hk : 1 ≤ k) (e K C b eps F : ℝ)
    (he : 0 ≤ e) (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : 0 ≤ b) (heps : 0 ≤ eps) (hF : 0 ≤ F)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal eps) :
    Integrable (fun ω => heatVHEATDriftRare k e K C b (R ω) (A ω) (T ω)) μ ∧
    (∫ ω,heatVHEATDriftRare k e K C b (R ω) (A ω) (T ω) ∂μ) ≤
      heatVHEATDriftFirstLine k e K C b eps 0 F := by
  by_cases hk1 : k=1
  · subst k
    have h1 := heatVHEATDrift_rare_moment μ R hR hR0 eps heps hR128 1 le_rfl (by norm_num)
    have h2 := heatVHEATDrift_rare_moment μ R hR hR0 eps heps hR128 2 (by norm_num) le_rfl
    let f := fun ω => (4*e*(2*K+2*b*C))*(R ω^1)+(4*e*C)*(R ω^2)
    have hi : Integrable f μ := (h1.1.const_mul _).add (h2.1.const_mul _)
    have heq : (fun ω => heatVHEATDriftRare 1 e K C b (R ω) (A ω) (T ω)) =ᵐ[μ] f := by
      filter_upwards [hTzero] with ω ht
      simp only [Pi.zero_apply] at ht
      dsimp only [f,heatVHEATDriftRare]
      rw [ht]
      norm_num
      ring
    refine ⟨hi.congr heq.symm,?_⟩
    rw [integral_congr_ae heq,integral_add (h1.1.const_mul _) (h2.1.const_mul _),integral_const_mul,integral_const_mul]
    have hc1 : 0 ≤ 4*e*(2*K+2*b*C) := by positivity
    have hc2 : 0 ≤ 4*e*C := by positivity
    have hh := add_le_add (mul_le_mul_of_nonneg_left h1.2 hc1) (mul_le_mul_of_nonneg_left h2.2 hc2)
    exact hh.trans_eq (by norm_num [heatVHEATDriftFirstLine,nativeHeatVHEATJ]; ring)
  · have hp : k-1≠0 := by omega
    have heq : (fun ω => heatVHEATDriftRare k e K C b (R ω) (A ω) (T ω)) =ᵐ[μ] 0 := by
      filter_upwards [hAzero] with ω ha
      simp only [Pi.zero_apply] at ha
      simp only [heatVHEATDriftRare,ha,zero_pow hp,zero_mul,mul_zero,Pi.zero_apply]
    have hi : Integrable (fun _ : Ω => (0:ℝ)) μ := integrable_const 0
    refine ⟨hi.congr heq.symm,?_⟩
    rw [integral_congr_ae heq]
    simp only [Pi.zero_apply,integral_zero]
    exact heatVHEATDrift_first_line_nonneg k e K C b eps 0 F he hK hC hb heps le_rfl hF

end
end ASDExplicitGamma.Native
