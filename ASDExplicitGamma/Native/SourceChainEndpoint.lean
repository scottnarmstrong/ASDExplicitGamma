module

public import ASDExplicitGamma.Native.SourceChainRows
public import ASDExplicitGamma.Scalar.UpperSource

/-! Part B endpoint caps from the proved Part C source owner at a completed
label below the outer induction target. All quantities retain the actual law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The six scalar endpoint mean and weak caps, obtained from the exact
rows by the proved theta-at-most-one adapter. -/
theorem native_scalar_endpoint_caps
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (m : ℤ) (hm : m < N) :
    (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
      ENNReal.ofReal (sourceMeanEndpointCaps r)) ∧
    (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
      ENNReal.ofReal (weakSourceEndpointCaps r)) :=
  scalar_endpoint_caps_of_source_rows M m hg
    (native_source_rows M h hM hg N hpast m hm)

/-- SC-SOURCE-ENDPOINT-COROLLARY: the actual OLD endpoint rows, the safe
actual depth-fourteen mean, and the separate full64 certificate tuple.
Every Part C producer premise is discharged under the chronology. -/
theorem native_scalar_source_endpoint_corollary
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (m : ℤ) (hm : m < N) :
    ordinaryMean M m ≤ ENNReal.ofReal (3/50 : ℝ) ∧
    nativeCompletedSourceMean M m 4 ≤ ENNReal.ofReal (sourceMeanEndpointCaps 4) ∧
    nativeCompletedSourceMean M m 5 ≤ ENNReal.ofReal (sourceMeanEndpointCaps 5) ∧
    nativeCompletedSourceWeak M m 5 ≤ ENNReal.ofReal (weakSourceEndpointCaps 5) ∧
    nativeCompletedSourceMean M m 14 ≤ ENNReal.ofReal safeDepth14EndpointCap ∧
    invFull64Bt < (1009309/500000 : ℚ) ∧
    invFull64KD < 16684 ∧ invFull64K0 < 5899542 ∧
    invS0 < (1130469/1000000 : ℚ) ∧ invS1 < (838143/200000 : ℚ) :=
  scalar_source_endpoint_full_tuple_of_smaller_gamma M m hg
    (native_source_smaller_gamma M h hM hg N hpast m hm)

/-- Retain theta in the actual depth-fourteen safe comparison before the
scalar endpoint relaxation. This compares the actual corrected mean with the
safe cap; it does not equate it with the plain-old upper-return formula. -/
theorem native_scalar_parent_fourteen_theta_endpoint
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (m : ℤ) (hm : m < N) :
    nativeCompletedSourceMean M m 14 ≤
      ENNReal.ofReal (theta M*safeDepth14EndpointCap) :=
  scalar_unpatched_parent14_cap_of_smaller_gamma M m
    (native_source_smaller_gamma M h hM hg N hpast m hm)

end
end ASDExplicitGamma.Native
