module

public import ASDExplicitGamma.Native.ParentWeakActualReturn
public import ASDExplicitGamma.Native.ParentWeakRareMajorant
public import ASDExplicitGamma.Native.OldSignedRareTailProduct
public import ASDExplicitGamma.Native.OldSignedRarePowerPayment

/-! Correlated rare bank powers multiplying the actual parent weak proxy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Response Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- Every non-leading bank power through order three multiplying W has a
complete theta-scaled payment, on the SAME simultaneous-band law. -/
theorem parent_weak_rare_weak_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hheight : 1 ≤ height) (hh16 : height ≤ 16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (depth : ℕ) (hdepth : depth=5) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (k : ℕ) (hk : k ≤ 3) :
    let R := nativeSourceBandRemainder M n height t
    let W := parentBoundaryBandWeakProxy M n height depth t
    Integrable (fun ω => rareExpansionTail (3683/2500) (R ω) 1 k*W ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,rareExpansionTail (3683/2500) (R ω) 1 k*W ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ (1/10^12:ℝ)*theta M := by
  intro R W
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := fun ω => (parentBoundaryBandMaxTraceHistory M n height (originCube 2 n) t ω).toReal
  let P := fun ω => rareExpansionTail (3683/2500) (R ω) 1 (k+1)*H ω
  have hb := native_source_band_local_bank M h hM hg n height hpast t ht.2
  have hsplit := native_source_band_history_rare_split M h hM hg n height hpast t ht.2
  have hH := parent_weak_actual_history_L2 M h hM hg (originCube 2 n) n 0 (by norm_num)
    (by simp only [originCube,Nat.cast_zero,sub_zero]) hstate height hheight hh16 hpast t ht
  have hC0 : 0 ≤ theta M*(10:ℝ)^16 := mul_nonneg (cold_theta_pos M).le (by norm_num)
  have hq := old_signed_rare_power_tail_payment R H (3683/2500) (3/10^46) (theta M*(10:ℝ)^16)
    (k+1) (by omega) (by norm_num) (by norm_num) hC0 hb.remainder_nonneg
    (fun _ => ENNReal.toReal_nonneg) hb.remainder_measurable.aestronglyMeasurable
    ((parent_boundary_band_extended_max_trace_measurable M n height (originCube 2 n) t).ennreal_toReal.aestronglyMeasurable)
    hsplit.2.2.2.1 hH.2
  have he : P=(fun ω => rareExpansionTail (3683/2500) (R ω) (H ω) (k+1)) :=
    funext (fun ω => (old_signed_rare_tail_linear _ _ _ _).symm)
  have hP : Integrable P μ := by rw [he]; exact hq.1
  have hPint : (∫ ω,P ω ∂μ) ≤ 13*(3/10^46:ℝ)*(theta M*(10:ℝ)^16) := by
    rw [he]
    exact hq.2.trans (old_signed_rare_power_thirteen _ _ (by norm_num) (by norm_num) hC0 (k+1) (by omega))
  have hm := parent_weak_actual_return M h hM hg n height hheight hh16 hpast hstate depth hdepth t ht
  have hR0 : ∀ ω,0 ≤ R ω := hb.remainder_nonneg
  have htail0 (ω) : 0 ≤ rareExpansionTail (3683/2500) (R ω) 1 k :=
    old_signed_rare_tail_nonneg _ _ _ (by norm_num) (hR0 ω) (by norm_num) k
  have hRm : AEStronglyMeasurable R μ := hb.remainder_measurable.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun ω => rareExpansionTail (3683/2500) (R ω) 1 k*W ω) μ := by
    apply AEStronglyMeasurable.mul _ hm.1.aestronglyMeasurable
    unfold rareExpansionTail
    exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ((hRm.pow i).const_mul _).mul_const 1)
  have hnonneg (ω) : 0 ≤ rareExpansionTail (3683/2500) (R ω) 1 k*W ω :=
    mul_nonneg (htail0 ω) (parent_weak_proxy_nonneg M n height depth t ω)
  have hmajor := parent_weak_actual_rare_majorant M h hM hg n height depth (by omega) hpast t ht.2
  have hle : ∀ᵐ ω ∂μ,rareExpansionTail (3683/2500) (R ω) 1 k*W ω ≤ 64*P ω := by
    filter_upwards [hmajor,hsplit.2.2.2.2] with ω hw hs
    have hx := (mul_le_mul_of_nonneg_left hs (htail0 ω)).trans
      (old_signed_rare_tail_next _ _ (by norm_num) (hR0 ω) k hk)
    calc
      _ ≤ rareExpansionTail (3683/2500) (R ω) 1 k*
          (64*(nativeSourceBandHistory M n height t ω).toReal*H ω) :=
        mul_le_mul_of_nonneg_left hw (htail0 ω)
      _ = 64*(rareExpansionTail (3683/2500) (R ω) 1 k*(nativeSourceBandHistory M n height t ω).toReal)*H ω := by ring
      _ ≤ 64*P ω := (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx (by norm_num : (0:ℝ)≤64)) ENNReal.toReal_nonneg).trans_eq (by dsimp only [P]; ring)
  have hi := (hP.const_mul 64).mono_nonneg hmeas (Filter.Eventually.of_forall hnonneg) hle
  refine ⟨hi,?_⟩
  have hh := integral_mono_ae hi (hP.const_mul 64) hle
  rw [integral_const_mul] at hh
  apply (hh.trans (mul_le_mul_of_nonneg_left hPint (by norm_num : (0:ℝ)≤64))).trans
  have hn : (64:ℝ)*13*(3/10^46)*(10:ℝ)^16 ≤ 1/10^12 := by norm_num
  convert mul_le_mul_of_nonneg_right hn (cold_theta_pos M).le using 1
  ring

end
end ASDExplicitGamma.Native
