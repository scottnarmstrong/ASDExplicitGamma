module

public import ASDExplicitGamma.Native.OldSignedTiledDepthPayment
public import ASDExplicitGamma.Native.OldSignedPartialInverseHistory
public import ASDExplicitGamma.Native.OldSignedTiledParentWeak
public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral

/-! Finite expectation of the entire shifted OLD weak history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- The genuine inverse-weighted parent trace on the source tiling. -/
def oldSignedActualTiledWeakProxy (M : ABKModel 2) (n : ℤ) (r : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  rawWeakTraceProxy
    (fun j => lemmaVInverseDepthMax (originCube 2 n) (oldSignedPartialFrameField M n 1 t ω) (r+j))
    (fun j => rawWeakTraceSequence M n (originCube 2 n) t ω (r+j))

/-- Every weighted history term is nonnegative on the actual insertion law. -/
theorem old_signed_tiled_history_term_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ inverseHistoryDiscount^(2*j)*lemmaVInverseDepthMax (originCube 2 n)
      (oldSignedPartialFrameField M n 1 t ω) (r+j)*
        rawWeakTraceSequence M n (originCube 2 n) t ω (r+j) :=
  mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
    (lemmaVInverseDepthMax_nonneg _ _ _)) (raw_weak_trace_sequence_nonneg M n _ t ht ω (r+j))

/-- Honest integrability and the complete common source budget. The entire
infinite history is paid before any real conversion or square root. -/
theorem old_signed_tiled_history_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) :
    Integrable (oldSignedActualTiledWeakProxy M n r t) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldSignedActualTiledWeakProxy M n r t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        2*((1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
          oldSignedSourceHistoryBudget M n (originCube 2 (n-(r:ℤ))) t j) := by
  let f := fun j ω => inverseHistoryDiscount^(2*j)*
    lemmaVInverseDepthMax (originCube 2 n) (oldSignedPartialFrameField M n 1 t ω) (r+j)*
      rawWeakTraceSequence M n (originCube 2 n) t ω (r+j)
  have hs (ω : Cutoff.CutoffSample 2) : Summable (fun j => f j ω) := by
    have hh := old_signed_shifted_weak_trace_proxy_summable (originCube 2 n) r
      (oldSignedPartialFrameField M n 1 t ω)
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 n))
        M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
        (oldSignedPartialResponseCoefficient n 1 t ω))
    simpa only [old_signed_one_shell_trace_depth M n t ω] using hh
  have hp (j : ℕ) := old_signed_tiled_depth_payment M h hM hg n r hr t ht hstates j
  have hb := (old_signed_source_history_budget_summable M h hM hg n r hr
    (originCube 2 (n-(r:ℤ))) rfl t ht hstates).mul_left 2
  have hh := old_signed_nonnegative_series_integral (Cutoff.cutoffSampleLaw M).toMeasure f
    (fun j => 2*(inverseHistoryDiscount^(2*j)*
      oldSignedSourceHistoryBudget M n (originCube 2 (n-(r:ℤ))) t j))
    (fun j => by simpa only [f,mul_assoc] using (hp j).1.const_mul (inverseHistoryDiscount^(2*j)))
    (old_signed_tiled_history_term_nonneg M n r t ht) hs hb (by
      intro j
      dsimp only [f]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      have hh := mul_le_mul_of_nonneg_left (hp j).2
        (pow_nonneg inverse_history_discount_range.1.le (2*j))
      exact hh.trans_eq (by ring))
  have hc : 0 ≤ 1-inverseHistoryDiscount^2 :=
    sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  change Integrable (fun ω => (1-inverseHistoryDiscount^2)*∑' j,f j ω) _ ∧ _
  refine ⟨hh.1.const_mul _,?_⟩
  change (∫ ω,(1-inverseHistoryDiscount^2)*∑' j,f j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ _
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hh.2 hc).trans_eq (by rw [tsum_mul_left]; ring)

end
end ASDExplicitGamma.Native
