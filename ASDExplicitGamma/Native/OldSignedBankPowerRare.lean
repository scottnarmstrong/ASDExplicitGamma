module

public import ASDExplicitGamma.Native.OldSignedRarePowerPayment
public import ASDExplicitGamma.Native.OldSignedBankDirectionalRare

/-! The actual local inverse bank pays the complete fourth-order rare tail. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Inverse Algsuperdiff.Section3 Numerics.Inverse
open scoped ENNReal
noncomputable section

/-- Actual correlated non-leading powers of the local-bank remainder cost
at most the literal source factor thirteen. All moment inputs come from the
bank and raw-trace transport, not from an estimate premise. -/
theorem old_signed_local_bank_rare_power_tail
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (hpast : ∀ l ≤ n,nativeInductionState M h l) (j k : ℕ) (hk : k≤4) :
    let T := fun ω => rawWeakTraceSequence M n (originCube 2 n) t ω j
    let C := theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
    Integrable (fun ω => rareExpansionTail (3683/2500) (oldSignedLocalBankRemainder M n t ω)
      (T ω) k) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,rareExpansionTail (3683/2500) (oldSignedLocalBankRemainder M n t ω) (T ω) k
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ 13*(3/10^46:ℝ)*C := by
  intro T C
  have hb := raw_shell_band_local_inverse_bank M h hM hg n 1 (by norm_num) t ht
    (fun l hl => hpast l hl.le)
  have htrace := (raw_trace_transport_profile_and_reserves_source M h hM hg n 0
    (by norm_num) t ht (fun d => hpast _ (by omega))).1 j
  simp only [Nat.cast_zero,sub_zero,ENNReal.ofReal_ofNat] at htrace
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0 ≤ (invTraceM:ℝ) := by exact_mod_cast hMrat
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : eLpNorm (oldSignedLocalBankRemainder M n t) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (3/10^46:ℝ) := by
    simpa only [oldSignedLocalBankRemainder,inverseBankReserve,Rat.cast_div,Rat.cast_pow,
      Rat.cast_ofNat] using hb.remainder_L128
  have hh := old_signed_rare_power_tail_payment (oldSignedLocalBankRemainder M n t) T
    (3683/2500) (3/10^46) C k hk (by norm_num) (by norm_num) hC hb.remainder_nonneg
    (fun ω => raw_weak_trace_sequence_nonneg M n (originCube 2 n) t ht ω j)
    hb.remainder_measurable.aestronglyMeasurable
    (old_signed_actual_trace_depth_integrable M n t ht j).aestronglyMeasurable hR htrace
  exact ⟨hh.1,hh.2.trans (old_signed_rare_power_thirteen _ C (by norm_num) (by norm_num) hC k hk)⟩

end
end ASDExplicitGamma.Native
