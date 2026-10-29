module

public import ASDExplicitGamma.Native.OldSignedQ1BankWeightedWeak
public import ASDExplicitGamma.Native.OldSignedSqrtExpectation

/-! Linear and mixed-root payments of the actual local inverse multiplier. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The actual common inverse multiplier times the weak root has its sharp
bank coefficient, obtained from the proved second bank-weighted moment. -/
theorem old_signed_q1_bank_weak_root
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    let B := rawShellBandLocalHistory M n 1 t
    let W := oldSignedActualTiledWeakProxy M n 5 t
    Integrable (fun ω => B ω*Real.sqrt (W ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,B ω*Real.sqrt (W ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (3683/2500:ℝ)*Real.sqrt (theta M*oldSignedQ1PanelXi t) := by
  intro B W
  have hh := old_signed_q1_bank_weighted_weak M h hM hg n hpast t ht 2 (by norm_num)
  have hr := old_signed_sqrt_expectation (Cutoff.cutoffSampleLaw M).toMeasure (fun ω => B ω^2*W ω) hh.1
    (fun ω => mul_nonneg (sq_nonneg (B ω)) (old_signed_actual_tiled_weak_proxy_nonneg M n 5 t ht ω))
  have he (ω) : Real.sqrt (B ω^2*W ω)=B ω*Real.sqrt (W ω) := by
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (show 0≤B ω from ENNReal.toReal_nonneg)]
  simp_rw [he] at hr
  refine ⟨hr.1,hr.2.trans (Real.sqrt_le_sqrt hh.2) |>.trans_eq ?_⟩
  rw [mul_assoc,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by norm_num : (0:ℝ)≤3683/2500)]

end
end ASDExplicitGamma.Native
