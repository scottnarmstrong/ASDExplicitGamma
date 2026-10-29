module

public import ASDExplicitGamma.Native.OldSignedActualPlusAmplitude
public import ASDExplicitGamma.Native.OldSignedActualMinusAmplitude

/-! Probability averaging of the direct sum of the actual affine proxies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- Both load families use one half-trace budget after their actual
covariance sums. The sum is integrable, not merely a real conversion. -/
theorem old_signed_actual_joint_mean_proxy_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (fun ω => oldSignedActualPlusMeanProxy M n r U hU t b L ω+
      oldSignedActualMinusMeanProxy M n r U hU t b L ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualPlusMeanProxy M n r U hU t b L ω+
      oldSignedActualMinusMeanProxy M n r U hU t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ((1-inverseHistoryDiscount^2)*
        ∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j)*
        (oldSignedFlatMeanSize (originCube 2 n) U b L true^2+
          oldSignedFlatMeanSize (originCube 2 n) U b L false^2) := by
  have hp := old_signed_actual_plus_mean_proxy_payment M h hM hg n r hr U hU t ht hstates b L
  have hm := old_signed_actual_minus_mean_proxy_payment M h hM hg n r hr U hU t ht hstates b L
  refine ⟨hp.1.add hm.1,?_⟩
  rw [integral_add hp.1 hm.1,mul_add]
  exact add_le_add hp.2 hm.2

end
end ASDExplicitGamma.Native
