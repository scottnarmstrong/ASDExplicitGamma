module

public import ASDExplicitGamma.Scalar.SourceEndpoint
public import ASDExplicitGamma.Scalar.HistoryDepthRandom
public import ASDExplicitGamma.Numerics.Inverse.Full64
public import ASDExplicitGamma.Numerics.Scalar.Upper

/-! Input caps for the Part B long-block upper trial. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open ASDExplicitGamma.Native ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics.Inverse
open Algsuperdiff.Section3
open scoped ENNReal

/-- The endpoint source rows, unpatched depth-14 parent input, and actual
depth-14 random history needed by the long-block upper trial. -/
theorem scalar_upper_source_caps_of_smaller_gamma
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hsource : NativeSourceSmallerGammaBounds M m)
    (hstate : ∀ k ≤ m, nativeInductionState M h k) :
    (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
        ENNReal.ofReal (sourceMeanEndpointCaps r)) ∧
      (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
        ENNReal.ofReal (weakSourceEndpointCaps r)) ∧
      nativeCompletedSourceMean M m 14 ≤ ENNReal.ofReal safeDepth14EndpointCap ∧
      eLpNorm (lagTraceHistory M m 14) 12 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (61 / 10 : ℝ) := by
  have hrows := native_source_rows_of_smaller_gamma M m hsource
  have hendpoints := scalar_endpoint_caps_of_source_rows M m hγ hrows
  have hp14θ := scalar_unpatched_parent14_cap_of_smaller_gamma M m hsource
  have hθ := ASDExplicitGamma.Cold.cold_theta_le_one M hγ
  have hsafe0 : 0 ≤ safeDepth14EndpointCap := by
    unfold safeDepth14EndpointCap
    positivity
  have hp14 : nativeCompletedSourceMean M m 14 ≤
      ENNReal.ofReal safeDepth14EndpointCap := by
    have hscale : theta M * safeDepth14EndpointCap ≤
        safeDepth14EndpointCap := by
      calc
        theta M * safeDepth14EndpointCap ≤
            1 * safeDepth14EndpointCap :=
          mul_le_mul_of_nonneg_right hθ hsafe0
        _ = safeDepth14EndpointCap := one_mul _
    calc
      nativeCompletedSourceMean M m 14 ≤
          ENNReal.ofReal (theta M * safeDepth14EndpointCap) := hp14θ
      _ ≤ ENNReal.ofReal safeDepth14EndpointCap :=
        ENNReal.ofReal_le_ofReal hscale
  have hhist := upper_depth_fourteen_random_history M h m
    (hstate m le_rfl) hθ
  exact ⟨hendpoints.1, hendpoints.2, hp14, hhist⟩

/-- The fixed full64 upper-trial response and history constants used alongside
the source caps. This is the exact outward rational tuple from the numerical
certificates, kept distinct from the full128 source profile. -/
theorem scalar_upper_full64_endpoint_caps :
    invFull64Bt < (1009309 / 500000 : ℚ) ∧
      invFull64KD < 16684 ∧ invFull64K0 < 5899542 ∧
      invS0 < (1130469 / 1000000 : ℚ) ∧
      invS1 < (838143 / 200000 : ℚ) := by
  have h64 := invFull64_caps
  have hhist := invFullHistory_caps
  have hBt : (2.018618 : ℚ) = 1009309 / 500000 := by norm_num
  have hS0 : (1.130469 : ℚ) = 1130469 / 1000000 := by norm_num
  have hS1 : (4.190715 : ℚ) = 838143 / 200000 := by norm_num
  refine ⟨?_, h64.2.1, h64.2.2, ?_, ?_⟩
  · rw [← hBt]
    exact h64.1
  · rw [← hS0]
    exact hhist.2.2.1
  · rw [← hS1]
    exact hhist.2.2.2

/-- The source endpoint's full consumer tuple, combining the exact
smaller-gamma conclusion with the independent full64 numerical certificate. -/
theorem scalar_source_endpoint_full_tuple_of_smaller_gamma
    (M : ABKModel 2) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hsource : NativeSourceSmallerGammaBounds M m) :
    ordinaryMean M m ≤ ENNReal.ofReal (3 / 50 : ℝ) ∧
      nativeCompletedSourceMean M m 4 ≤
        ENNReal.ofReal (sourceMeanEndpointCaps (⟨4, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceMean M m 5 ≤
        ENNReal.ofReal (sourceMeanEndpointCaps (⟨5, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceWeak M m 5 ≤
        ENNReal.ofReal (weakSourceEndpointCaps (⟨5, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceMean M m 14 ≤ ENNReal.ofReal safeDepth14EndpointCap ∧
      invFull64Bt < (1009309 / 500000 : ℚ) ∧
      invFull64KD < 16684 ∧ invFull64K0 < 5899542 ∧
      invS0 < (1130469 / 1000000 : ℚ) ∧
      invS1 < (838143 / 200000) := by
  have hsourceCaps := scalar_source_endpoint_corollary_of_smaller_gamma
    M m hγ hsource
  have hfull := scalar_upper_full64_endpoint_caps
  exact ⟨hsourceCaps.1, hsourceCaps.2.1, hsourceCaps.2.2.1,
    hsourceCaps.2.2.2.1, hsourceCaps.2.2.2.2,
    hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2⟩

/-- The endpoint data and certified UPPER error constant,
assembled from the exact smaller-gamma producer output. -/
theorem scalar_upper_endpoint_domination_caps_of_smaller_gamma
    (M : ABKModel 2) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hsource : NativeSourceSmallerGammaBounds M m) :
    (ordinaryMean M m ≤ ENNReal.ofReal (3 / 50 : ℝ) ∧
      nativeCompletedSourceMean M m 4 ≤
        ENNReal.ofReal (sourceMeanEndpointCaps (⟨4, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceMean M m 5 ≤
        ENNReal.ofReal (sourceMeanEndpointCaps (⟨5, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceWeak M m 5 ≤
        ENNReal.ofReal (weakSourceEndpointCaps (⟨5, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceMean M m 14 ≤ ENNReal.ofReal safeDepth14EndpointCap ∧
      invFull64Bt < (1009309 / 500000 : ℚ) ∧
      invFull64KD < 16684 ∧ invFull64K0 < 5899542 ∧
      invS0 < (1130469 / 1000000 : ℚ) ∧
      invS1 < (838143 / 200000 : ℚ)) ∧
      ASDExplicitGamma.Numerics.Mirror.evalReal
        ASDExplicitGamma.Numerics.Scalar.scalarRealEnv
        ASDExplicitGamma.Numerics.Scalar.upperErrorExpr < (681 / 10000 : ℝ) := by
  exact ⟨scalar_source_endpoint_full_tuple_of_smaller_gamma M m hγ hsource,
    ASDExplicitGamma.Numerics.Scalar.upper_error_bounds.1⟩

end ASDExplicitGamma.Scalar
