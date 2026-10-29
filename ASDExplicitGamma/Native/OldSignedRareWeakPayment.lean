module

public import ASDExplicitGamma.Native.OldSignedRareTailProduct
public import ASDExplicitGamma.Native.OldSignedQuarterRareHistory
public import ASDExplicitGamma.Native.OldSignedActualWeakMajorant
public import ASDExplicitGamma.Native.OldSignedQ1WeakEnvelope

/-! Every rare bank-weighted actual weak term fits the fixed theta reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The actual complete weak energy multiplied by any of the first three
non-leading inverse powers is integrable and has its full correlated payment. -/
theorem old_signed_actual_rare_weak_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (k : ℕ) (hk : k≤3) :
    let R := oldSignedLocalBankRemainder M n t
    let W := oldSignedActualTiledWeakProxy M n 5 t
    Integrable (fun ω => rareExpansionTail (3683/2500) (R ω) 1 k*W ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,rareExpansionTail (3683/2500) (R ω) 1 k*W ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤(1/10^12:ℝ)*theta M := by
  intro R W
  let P := fun ω => rareExpansionTail (3683/2500) (R ω) 1 (k+1)*oldSignedActualQuarterTrace M n t ω
  have hb := raw_shell_band_local_inverse_bank M h hM hg n 1 (by norm_num) t ht (fun l hl => hpast l hl.le)
  have hq := old_signed_local_bank_quarter_rare_history M h hM hg n t ht hpast (k+1) (by omega)
  simp_rw [old_signed_quarter_rare_factor] at hq
  have hP : Integrable P (Cutoff.cutoffSampleLaw M).toMeasure := hq.1
  have hm := old_signed_actual_q1_panel_weak M h hM hg n hpast t ht
  have hR0 : ∀ ω,0≤R ω := hb.remainder_nonneg
  have htail0 (ω) : 0≤rareExpansionTail (3683/2500) (R ω) 1 k :=
    old_signed_rare_tail_nonneg _ _ _ (by norm_num) (hR0 ω) (by norm_num) k
  have hRm : AEStronglyMeasurable R (Cutoff.cutoffSampleLaw M).toMeasure :=
    hb.remainder_measurable.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun ω => rareExpansionTail (3683/2500) (R ω) 1 k*W ω)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply AEStronglyMeasurable.mul _ hm.1.aestronglyMeasurable
    unfold rareExpansionTail
    exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ((hRm.pow i).const_mul _).mul_const 1)
  have hnonneg (ω) : 0≤rareExpansionTail (3683/2500) (R ω) 1 k*W ω :=
    mul_nonneg (htail0 ω) (old_signed_actual_tiled_weak_proxy_nonneg M n 5 t ht ω)
  have hmajor := old_signed_actual_q1_weak_rare_majorant M h hM hg n (fun l hl => hpast l hl.le) t ht
  have hsplit := old_signed_actual_cell_inverse_history_split M h hM hg n (fun l hl => hpast l hl.le)
    0 (by norm_num) (originCube 2 n) (by simp only [descendantsAtDepth_zero,Finset.mem_singleton]) t ht
  have hle : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      rareExpansionTail (3683/2500) (R ω) 1 k*W ω≤32*P ω := by
    filter_upwards [hmajor,hsplit] with ω hw hs
    have hH := old_signed_actual_quarter_trace_nonneg M n t ht ω
    have hx := (mul_le_mul_of_nonneg_left hs.2 (htail0 ω)).trans
      (old_signed_rare_tail_next _ _ (by norm_num) (hR0 ω) k hk)
    calc
      _ ≤ rareExpansionTail (3683/2500) (R ω) 1 k*
          (32*rawShellBandLocalHistory M n 1 t ω*oldSignedActualQuarterTrace M n t ω) :=
        mul_le_mul_of_nonneg_left hw (htail0 ω)
      _ = 32*(rareExpansionTail (3683/2500) (R ω) 1 k*rawShellBandLocalHistory M n 1 t ω)*
          oldSignedActualQuarterTrace M n t ω := by ring
      _ ≤ 32*P ω := (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx (by norm_num : (0:ℝ)≤32)) hH).trans_eq (by dsimp only [P]; ring)
  have hi := (hP.const_mul 32).mono_nonneg hmeas (Filter.Eventually.of_forall hnonneg) hle
  refine ⟨hi,?_⟩
  have hh := integral_mono_ae hi (hP.const_mul 32) hle
  rw [integral_const_mul] at hh
  apply (hh.trans (mul_le_mul_of_nonneg_left hq.2 (by norm_num : (0:ℝ)≤32))).trans
  have hn : (32:ℝ)*(1/10^30)≤1/10^12 := by norm_num
  convert mul_le_mul_of_nonneg_right hn (cold_theta_pos M).le using 1
  ring

end
end ASDExplicitGamma.Native
