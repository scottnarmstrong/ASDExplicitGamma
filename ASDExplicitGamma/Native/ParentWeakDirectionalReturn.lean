module

public import ASDExplicitGamma.Native.ParentWeakBudget
public import ASDExplicitGamma.Native.ParentWeakDirectionalDepth
public import ASDExplicitGamma.Native.ParentBoundaryBandDirectionalHistory

/-! Actual directional proxy expectations preserving the half-trace factor. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Inverse Variational Cold Algsuperdiff.Section3
noncomputable section

/-- The complete inverse-weighted directional history has a finite expectation,
paid by half the deterministic trace history plus the full correlated reserve. -/
theorem parent_weak_directional_history_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) (r : ℕ) (hr : r=5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n) (e : Vec 2) :
    Integrable (fun ω => ∑' j,parentBoundaryBandDirectionalHistoryTerm M n height U t e j ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,∑' j,parentBoundaryBandDirectionalHistoryTerm M n height U t e j ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (∑' j : ℕ,inverseHistoryDiscount^(2*j)*parentWeakDirectionalBudget M n height U t j)*vecNormSq e := by
  have hbud := parent_weak_directional_budget_return M h hM hg n height hheight hpast hstate r hr U hU t ht
  have hf (j : ℕ) := parent_weak_directional_depth_payment M h hM hg n height hheight hh16 r (by omega) U hU t ht hpast hstate j e
  have hh := old_signed_nonnegative_series_integral (Cutoff.cutoffSampleLaw M).toMeasure
    (parentBoundaryBandDirectionalHistoryTerm M n height U t e)
    (fun j => (inverseHistoryDiscount^(2*j)*parentWeakDirectionalBudget M n height U t j)*vecNormSq e)
    (fun j => (hf j).1.const_mul _)
    (parent_boundary_band_directional_history_term_nonneg M n height r U hU t e)
    (parent_boundary_band_directional_history_summable M n height r U hU t e)
    (hbud.1.mul_right _) (by
      intro j
      unfold parentBoundaryBandDirectionalHistoryTerm
      rw [integral_const_mul]
      have hle := mul_le_mul_of_nonneg_left (hf j).2
        (pow_nonneg inverse_history_discount_range.1.le (2*j))
      simpa only [parentWeakDirectionalBudget,mul_assoc] using hle)
  rw [tsum_mul_right] at hh
  exact hh

/-- The normalized physical directional proxy has the same complete
half-trace budget; no infinite extended history is converted to zero. -/
theorem parent_weak_directional_proxy_budget_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) (r : ℕ) (hr : r=5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n) (e : Vec 2) :
    Integrable (fun ω => oldSignedDirectionalProxy U
      (parentBoundaryBandFrameField M n height t ω) e) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedDirectionalProxy U (parentBoundaryBandFrameField M n height t ω) e
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ((1-inverseHistoryDiscount^2)*
        ∑' j : ℕ,inverseHistoryDiscount^(2*j)*parentWeakDirectionalBudget M n height U t j)*vecNormSq e := by
  have hh := parent_weak_directional_history_payment M h hM hg n height hheight hh16 r hr U hU t ht hpast hstate e
  have hc : 0 ≤ 1-inverseHistoryDiscount^2 :=
    sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have he (ω : Cutoff.CutoffSample 2) : oldSignedDirectionalProxy U
      (parentBoundaryBandFrameField M n height t ω) e =
      (1-inverseHistoryDiscount^2)*∑' j,parentBoundaryBandDirectionalHistoryTerm M n height U t e j ω := by
    simp only [oldSignedDirectionalProxy,rawWeakTraceProxy,parentBoundaryBandDirectionalHistoryTerm,mul_assoc]
  simp_rw [he]
  refine ⟨hh.1.const_mul _,?_⟩
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hh.2 hc).trans_eq (by ring)


/-- Sharp actual-law directional return on every source cell. Its half-trace
leading factor and entire reserve both retain theta. -/
theorem parent_weak_directional_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hheight : 1 ≤ height) (hheight16 : height ≤ 16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (depth : ℕ) (hdepth : depth=5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) depth)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (e : Vec 2) :
    Integrable (fun ω => oldSignedDirectionalProxy U (parentBoundaryBandFrameField M n height t ω) e)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedDirectionalProxy U (parentBoundaryBandFrameField M n height t ω) e
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (theta M/2)*((23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+2/10^12)*vecNormSq e := by
  have hw := parent_weak_directional_proxy_budget_payment M h hM hg n height hheight hheight16
    depth hdepth U hU t ht hpast hstate e
  have hb := parent_weak_directional_budget_return M h hM hg n height hheight hpast hstate depth hdepth U hU t ht
  refine ⟨hw.1,hw.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (vecNormSq_nonneg e)
  exact hb.2.trans (mul_le_mul_of_nonneg_left
    (by linarith : (23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+1/10^12 ≤
      (23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+2/10^12)
    (div_nonneg (cold_theta_pos M).le (by norm_num)))

end
end ASDExplicitGamma.Native
