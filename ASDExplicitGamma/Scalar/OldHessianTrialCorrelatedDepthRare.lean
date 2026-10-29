module

public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedLocalReal
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalTraceMoments
public import ASDExplicitGamma.Inverse.ParentGapHolder

/-! Joint Holder payments for the actual global bank, grouped OLD local
rare remainder and literal large-parent trace. The generic real-integral
conversion adapts the established local weighted-Theta argument. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

theorem old_hessian_correlated_depth_rare_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B R T : Ω → ℝ) (β ε C : ℝ) (k : ℕ) (hk : k ≤ 3)
    (hβ : 0 ≤ β) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hB0 : ∀ ω, 0 ≤ B ω) (hR0 : ∀ ω, 0 ≤ R ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (hBmeas : AEStronglyMeasurable B μ) (hRmeas : AEStronglyMeasurable R μ)
    (hTmeas : AEStronglyMeasurable T μ)
    (hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => B ω ^ k * R ω * T ω) μ ∧
      (∫ ω, B ω ^ k * R ω * T ω ∂μ) ≤ β ^ k * ε * C := by
  have hholder := parent_gap_global_local_rare_term B R T β ε C k hk
    hB0 hR0 hT0 hBmeas hRmeas hTmeas hB128 hR128 hT2
  have hnonneg (ω : Ω) : 0 ≤ B ω ^ k * R ω * T ω :=
    mul_nonneg (mul_nonneg (pow_nonneg (hB0 ω) k) (hR0 ω)) (hT0 ω)
  have hreal (ω : Ω) :
      ENNReal.ofReal (B ω ^ k * R ω * T ω) =
        ENNReal.ofReal (B ω) ^ k * ENNReal.ofReal (R ω) * ENNReal.ofReal (T ω) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (hB0 ω) k) (hR0 ω)),
      ENNReal.ofReal_mul (pow_nonneg (hB0 ω) k), ENNReal.ofReal_pow (hB0 ω)]
  have hbound : ∫⁻ ω, ENNReal.ofReal (B ω ^ k * R ω * T ω) ∂μ ≤
      ENNReal.ofReal (β ^ k * ε * C) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (B ω) ^ k * ENNReal.ofReal (R ω) *
            ENNReal.ofReal (T ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with ω
        exact hreal ω
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal β ^ k * ENNReal.ofReal ε) := hholder
      _ = ENNReal.ofReal (β ^ k * ε * C) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hβ k) hε),
          ENNReal.ofReal_mul (pow_nonneg hβ k), ENNReal.ofReal_pow hβ]
        ring
  have hmeas : AEStronglyMeasurable
      (fun ω => B ω ^ k * R ω * T ω) μ := (hBmeas.pow k).mul hRmeas |>.mul hTmeas
  have hi : Integrable (fun ω => B ω ^ k * R ω * T ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall hnonneg)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall hnonneg)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (pow_nonneg hβ k) hε) hC)).mp hbound

/-- Actual depthwise correlated local-rare payment, with every bank,
measurability and moment input supplied from completed states. -/
theorem old_hessian_actual_correlated_depth_rare
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (j k : ℕ) (hk : k≤3) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let T := fun ω => rawWeakTraceSequence M m (originCube 2 (m+129)) 0 ω (134+j)
    Integrable (fun ω => oldHessianGroupedBank M m ω^k*oldHessianLocalDepthRare M m j ω*T ω) μ ∧
    (∫ ω,oldHessianGroupedBank M m ω^k*oldHessianLocalDepthRare M m j ω*T ω ∂μ) ≤
      (14103/10000:ℝ)^k*(5*inverseBankDepthReserve .localInverse M j)*
        (theta M*(Numerics.Inverse.invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)) := by
  intro μ T
  have hglobal := old_hessian_actual_grouped_real_bank M h hM hg N hpast m hm
  have hlocal := old_hessian_actual_local_depth_rare M h hM hg N hpast m hm j
  have hT2 := old_hessian_large_parent_trace_profile M h hM hg N hpast m hm 5 (by norm_num) j
  have hC0 : 0≤theta M*(Numerics.Inverse.invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j) := by
    have hθ := (cold_theta_pos M).le
    have hMrat : 0≤Numerics.Inverse.invTraceM := by rw [Numerics.Inverse.invTrace_coefficient.1]; positivity
    have hM0 : 0≤(Numerics.Inverse.invTraceM:ℝ) := by exact_mod_cast hMrat
    positivity
  have hε0 : 0≤5*inverseBankDepthReserve .localInverse M j := by
    unfold inverseBankDepthReserve
    have hr : 0≤(inverseBankReserve .localInverse:ℝ) := by norm_num [inverseBankReserve]
    have hf := (bankDepthFrame_pos M j).le
    positivity
  exact old_hessian_correlated_depth_rare_integrable (oldHessianGroupedBank M m)
    (oldHessianLocalDepthRare M m j) T (14103/10000:ℝ)
    (5*inverseBankDepthReserve .localInverse M j)
    (theta M*(Numerics.Inverse.invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)) k hk
    (by norm_num) hε0 hC0 (fun _ => ENNReal.toReal_nonneg) hlocal.2.1
    (fun ω => raw_weak_trace_sequence_nonneg M m (originCube 2 (m+129)) 0 (by norm_num) ω (134+j))
    hglobal.1.aestronglyMeasurable hlocal.1.aestronglyMeasurable
    (old_signed_source_trace_integrable M m (originCube 2 (m+129)) 0 (by norm_num) (134+j)).1
    hglobal.2.2.1 hlocal.2.2 hT2

end
end ASDExplicitGamma.Scalar
