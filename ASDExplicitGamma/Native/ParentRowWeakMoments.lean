module

public import ASDExplicitGamma.Native.ParentRowWeakAllowance
public import ASDExplicitGamma.Native.ParentRowDerivativeProfiles
public import ASDExplicitGamma.Native.ParentWeakBankWeightedReturn
public import ASDExplicitGamma.Native.OldSignedSqrtExpectation

/-! Sharp weak and bank-root moments on the simultaneous parent band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The actual weak expectation fits the shared primitive allowance. -/
theorem parent_row_weak_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    Integrable (parentBoundaryBandWeakProxy M n height r t) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentBoundaryBandWeakProxy M n height r t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      theta M*parentRowWeakAllowance height t := by
  have hh := parent_weak_bank_weighted_return M h hM hg n height hheight hh16 hpast hstate r hr t ht 0 (by norm_num)
  simpa only [pow_zero,one_mul,parentRowWeakAllowance] using hh

/-- The common bank times the weak root is paid by the sharp second
bank-weighted moment on the same actual sample law. -/
theorem parent_row_bank_weak_root
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    let B := fun ω => (nativeSourceBandHistory M n height t ω).toReal
    let W := parentBoundaryBandWeakProxy M n height r t
    Integrable (fun ω => B ω*Real.sqrt (W ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,B ω*Real.sqrt (W ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (3683/2500:ℝ)*Real.sqrt (theta M*parentRowWeakAllowance height t) := by
  intro B W
  have hh := parent_weak_bank_weighted_return M h hM hg n height hheight hh16 hpast hstate r hr t ht 2 (by norm_num)
  have hw := old_signed_sqrt_expectation (Cutoff.cutoffSampleLaw M).toMeasure (fun ω => B ω^2*W ω) hh.1
    (fun ω => mul_nonneg (sq_nonneg _) (parent_row_weak_proxy_nonneg M n height r t ω))
  have he (ω) : Real.sqrt (B ω^2*W ω)=B ω*Real.sqrt (W ω) := by
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (show 0≤B ω from ENNReal.toReal_nonneg)]
  simp_rw [he] at hw
  refine ⟨hw.1,(hw.2.trans (Real.sqrt_le_sqrt hh.2)).trans_eq ?_⟩
  rw [mul_assoc,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by norm_num : (0:ℝ)≤3683/2500)]
  rfl

end
end ASDExplicitGamma.Native
