module

public import ASDExplicitGamma.Native.ParentWeakRareWeak

/-! Sharp bank powers on the actual simultaneous parent weak proxy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- Actual simultaneous-band bank-weighted weak moments, keeping the literal
leading b^k and paying every correlated rare power with one theta. -/
theorem parent_weak_bank_weighted_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hheight : 1 ≤ height) (hheight16 : height ≤ 16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (depth : ℕ) (hdepth : depth=5) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (k : ℕ) (hk : k ≤ 3) :
    let B := fun ω => (nativeSourceBandHistory M n height t ω).toReal
    let W := parentBoundaryBandWeakProxy M n height depth t
    Integrable (fun ω => B ω^k*W ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,B ω^k*W ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (3683/2500:ℝ)^k*theta M*
          ((23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+(2/10^12:ℝ)) := by
  intro B W
  let R := nativeSourceBandRemainder M n height t
  let Tail := fun ω => rareExpansionTail (3683/2500) (R ω) 1 k*W ω
  have hw := parent_weak_actual_return M h hM hg n height hheight hheight16 hpast hstate depth hdepth t ht
  have hr := parent_weak_rare_weak_payment M h hM hg n height hheight hheight16 hpast hstate depth hdepth t ht k hk
  have hsplit := native_source_band_history_rare_split M h hM hg n height hpast t ht.2
  have hpoint : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      B ω^k*W ω ≤ (3683/2500:ℝ)^k*W ω+Tail ω := by
    filter_upwards [hsplit.2.2.2.2] with ω hω
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ENNReal.toReal_nonneg hω k)
      (parent_weak_proxy_nonneg M n height depth t ω)
    exact hh.trans_eq (by
      rw [old_signed_rare_power_binomial _ _ _ k (by omega),old_signed_rare_tail_linear])
  have hmajor := (hw.1.const_mul ((3683/2500:ℝ)^k)).add hr.1
  have hi := hmajor.mono_nonneg
    (((native_source_band_history_toReal_measurable M n height t).aestronglyMeasurable.pow k).mul hw.1.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (pow_nonneg ENNReal.toReal_nonneg k)
      (parent_weak_proxy_nonneg M n height depth t ω))) hpoint
  have hint := integral_mono_ae hi hmajor hpoint
  simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply] at hint
  rw [integral_add (hw.1.const_mul _) hr.1,integral_const_mul] at hint
  have hlead : 1 ≤ (3683/2500:ℝ)^k := one_le_pow₀ (by norm_num)
  have hreserve : (1/10^12:ℝ)*theta M ≤ (3683/2500:ℝ)^k*((1/10^12:ℝ)*theta M) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hlead
      (mul_nonneg (by norm_num) (cold_theta_pos M).le)
  refine ⟨hi,?_⟩
  calc
    _ ≤ (3683/2500:ℝ)^k*(theta M*((23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+1/10^12))+
        (1/10^12:ℝ)*theta M :=
      hint.trans (add_le_add (mul_le_mul_of_nonneg_left hw.2 (by positivity)) hr.2)
    _ ≤ (3683/2500:ℝ)^k*(theta M*((23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+1/10^12))+
        (3683/2500:ℝ)^k*((1/10^12:ℝ)*theta M) := add_le_add le_rfl hreserve
    _ = _ := by ring

end
end ASDExplicitGamma.Native
