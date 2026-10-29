module

public import ASDExplicitGamma.Native.OldSignedRareWeakPayment

/-! Sharp leading inverse powers multiplying the complete actual weak history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The unchanged Xi field has room for both the depth rare payment and the
non-leading powers of the common inverse bank. -/
theorem old_signed_q1_xi_two_reserves (t : ℝ) (ht : 0≤t) :
    (23/100:ℝ)+(9/500)*t+2/10^12≤oldSignedQ1PanelXi t := by
  have hh := add_le_add old_signed_q1_mean_setup_lower.2.2.1
    (mul_le_mul_of_nonneg_left old_signed_q1_mean_setup_lower.2.2.2 ht)
  change _≤Numerics.Native.nativeSetupQ1001FieldsR.getD 15 0+
    t*Numerics.Native.nativeSetupQ1001FieldsR.getD 12 0
  linarith only [hh]

/-- All bank-weighted weak moments used by the AN spatial bill have the
literal leading bank powers. The complete correlated rare terms are paid
inside the fixed Xi reserve, with no bank estimate as a premise. -/
theorem old_signed_q1_bank_weighted_weak
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (k : ℕ) (hk : k≤3) :
    let B := rawShellBandLocalHistory M n 1 t
    let W := oldSignedActualTiledWeakProxy M n 5 t
    Integrable (fun ω => B ω^k*W ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,B ω^k*W ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (3683/2500:ℝ)^k*theta M*oldSignedQ1PanelXi t := by
  intro B W
  let R := oldSignedLocalBankRemainder M n t
  let Tail := fun ω => rareExpansionTail (3683/2500) (R ω) 1 k*W ω
  have hw := old_signed_actual_q1_panel_weak M h hM hg n hpast t ht
  have hr := old_signed_actual_rare_weak_payment M h hM hg n hpast t ht k hk
  have hsplit := old_signed_actual_cell_inverse_history_split M h hM hg n (fun l hl => hpast l hl.le)
    0 (by norm_num) (originCube 2 n) (by simp only [descendantsAtDepth_zero,Finset.mem_singleton]) t ht
  have hpoint : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      B ω^k*W ω≤(3683/2500:ℝ)^k*W ω+Tail ω := by
    filter_upwards [hsplit] with ω hω
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ENNReal.toReal_nonneg hω.2 k)
      (old_signed_actual_tiled_weak_proxy_nonneg M n 5 t ht ω)
    exact hh.trans_eq (by
      rw [old_signed_rare_power_binomial _ _ _ k (by omega),old_signed_rare_tail_linear])
  have hmajor := (hw.1.const_mul ((3683/2500:ℝ)^k)).add hr.1
  have hi := hmajor.mono_nonneg
    (((old_signed_local_history_measurable M n t).aestronglyMeasurable.pow k).mul hw.1.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (pow_nonneg ENNReal.toReal_nonneg k)
      (old_signed_actual_tiled_weak_proxy_nonneg M n 5 t ht ω))) hpoint
  have hwcoarse := (old_signed_tiled_history_payment M h hM hg n 5 (by norm_num) t ht hpast).2.trans
    (old_signed_q1_source_history_affine_budget M h hM hg n hpast (originCube 2 (n-5)) rfl t ht)
  have hint := integral_mono_ae hi hmajor hpoint
  simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply] at hint
  rw [integral_add (hw.1.const_mul _) hr.1,integral_const_mul] at hint
  have hlead : 1≤(3683/2500:ℝ)^k := one_le_pow₀ (by norm_num)
  have hreserve : (1/10^12:ℝ)*theta M≤(3683/2500:ℝ)^k*((1/10^12:ℝ)*theta M) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hlead
      (mul_nonneg (by norm_num) (cold_theta_pos M).le)
  refine ⟨hi,?_⟩
  calc
    _ ≤ (3683/2500:ℝ)^k*(theta M*((23/100:ℝ)+(9/500)*t+1/10^12))+(1/10^12:ℝ)*theta M :=
      hint.trans (add_le_add (mul_le_mul_of_nonneg_left hwcoarse (by positivity)) hr.2)
    _ ≤ (3683/2500:ℝ)^k*(theta M*((23/100:ℝ)+(9/500)*t+1/10^12))+
        (3683/2500:ℝ)^k*((1/10^12:ℝ)*theta M) := add_le_add le_rfl hreserve
    _ = (3683/2500:ℝ)^k*theta M*((23/100:ℝ)+(9/500)*t+2/10^12) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (old_signed_q1_xi_two_reserves t ht.1)
      (mul_nonneg (by positivity) (cold_theta_pos M).le)

end
end ASDExplicitGamma.Native
