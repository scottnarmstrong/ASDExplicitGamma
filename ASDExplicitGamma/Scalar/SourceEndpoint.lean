module

public import ASDExplicitGamma.Scalar.SourceEndpointAdapter
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Cold.NativeThetaScaling

/-! Part B endpoint adapters over the exact native source rows. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open ASDExplicitGamma.Native ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Section3
open scoped ENNReal

private theorem source_mean_cap_eq (r : Fin 6) :
    ((nativeCompletedMeanCaps.getD r.val 0 : ℚ) : ℝ) =
      sourceMeanEndpointCaps r := by
  fin_cases r <;> norm_num [nativeCompletedMeanCaps, sourceMeanEndpointCaps]

private theorem source_weak_cap_eq (r : Fin 6) :
    ((nativeCompletedWeakCaps.getD r.val 0 : ℚ) : ℝ) =
      weakSourceEndpointCaps r := by
  fin_cases r <;> norm_num [nativeCompletedWeakCaps, weakSourceEndpointCaps]

private theorem source_mean_endpoint_cap_nonneg (r : Fin 6) :
    0 ≤ sourceMeanEndpointCaps r := by
  fin_cases r <;> norm_num [sourceMeanEndpointCaps]

private theorem source_weak_endpoint_cap_nonneg (r : Fin 6) :
    0 ≤ weakSourceEndpointCaps r := by
  fin_cases r <;> norm_num [weakSourceEndpointCaps]

/-- The exact NA-SOURCE-ROWS conclusion gives the unscaled six-row endpoint
caps used by the scalar upper bounds. The only scaling step is `theta ≤ 1` from
the producer's stated smaller-gamma range. -/
theorem scalar_endpoint_caps_of_source_rows
    (M : ABKModel 2) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hrows : NativeSourceRowsBounds M m) :
    (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
        ENNReal.ofReal (sourceMeanEndpointCaps r)) ∧
      (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
        ENNReal.ofReal (weakSourceEndpointCaps r)) := by
  have hθ := ASDExplicitGamma.Cold.cold_theta_le_one M hγ
  constructor
  · intro r
    have hc := source_mean_cap_eq r
    have hscale : theta M * sourceMeanEndpointCaps r ≤
        sourceMeanEndpointCaps r := by
      calc
        theta M * sourceMeanEndpointCaps r ≤
            1 * sourceMeanEndpointCaps r :=
          mul_le_mul_of_nonneg_right hθ (source_mean_endpoint_cap_nonneg r)
        _ = sourceMeanEndpointCaps r := one_mul _
    calc
      nativeCompletedSourceMean M m r.val ≤
          ENNReal.ofReal (theta M *
            ((nativeCompletedMeanCaps.getD r.val 0 : ℚ) : ℝ)) := hrows.mean r
      _ = ENNReal.ofReal (theta M * sourceMeanEndpointCaps r) := by rw [hc]
      _ ≤ ENNReal.ofReal (sourceMeanEndpointCaps r) := ENNReal.ofReal_le_ofReal hscale
  · intro r
    have hc := source_weak_cap_eq r
    have hscale : theta M * weakSourceEndpointCaps r ≤
        weakSourceEndpointCaps r := by
      calc
        theta M * weakSourceEndpointCaps r ≤
            1 * weakSourceEndpointCaps r :=
          mul_le_mul_of_nonneg_right hθ (source_weak_endpoint_cap_nonneg r)
        _ = weakSourceEndpointCaps r := one_mul _
    calc
      nativeCompletedSourceWeak M m r.val ≤
          ENNReal.ofReal (theta M *
            ((nativeCompletedWeakCaps.getD r.val 0 : ℚ) : ℝ)) := hrows.weak r
      _ = ENNReal.ofReal (theta M * weakSourceEndpointCaps r) := by rw [hc]
      _ ≤ ENNReal.ofReal (weakSourceEndpointCaps r) := ENNReal.ofReal_le_ofReal hscale

/-- The same endpoint adapter instantiated with the exact named
NA-SOURCE-SMALLER-GAMMA conclusion. This stays a helper until the smaller-gamma source conclusion
and the other endpoint inputs are supplied. -/
theorem scalar_endpoint_caps_of_smaller_gamma
    (M : ABKModel 2) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hsource : NativeSourceSmallerGammaBounds M m) :
    (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
        ENNReal.ofReal (sourceMeanEndpointCaps r)) ∧
      (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
        ENNReal.ofReal (weakSourceEndpointCaps r)) :=
  scalar_endpoint_caps_of_source_rows M m hγ
    (native_source_rows_of_smaller_gamma M m hsource)

/-- The four completed OLD rows used by the scalar endpoint comparison,
including the exact depth-four, depth-five, and retained weak depth-five
source outputs. -/
theorem scalar_old_endpoint_rows_of_smaller_gamma
    (M : ABKModel 2) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hsource : NativeSourceSmallerGammaBounds M m) :
    ordinaryMean M m ≤ ENNReal.ofReal (3 / 50 : ℝ) ∧
      nativeCompletedSourceMean M m 4 ≤
        ENNReal.ofReal (sourceMeanEndpointCaps (⟨4, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceMean M m 5 ≤
        ENNReal.ofReal (sourceMeanEndpointCaps (⟨5, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceWeak M m 5 ≤
        ENNReal.ofReal (weakSourceEndpointCaps (⟨5, by omega⟩ : Fin 6)) := by
  have hcaps := scalar_endpoint_caps_of_smaller_gamma M m hγ hsource
  have hmean0 := hcaps.1 (0 : Fin 6)
  have hcap0 : sourceMeanEndpointCaps (0 : Fin 6) = 3 / 50 := by
    norm_num [sourceMeanEndpointCaps]
  have hord : ordinaryMean M m ≤ ENNReal.ofReal (3 / 50 : ℝ) := by
    rw [← native_completed_source_mean_zero M m]
    simpa [hcap0] using hmean0
  exact ⟨hord, hcaps.1 (⟨4, by omega⟩ : Fin 6),
    hcaps.1 (⟨5, by omega⟩ : Fin 6), hcaps.2 (⟨5, by omega⟩ : Fin 6)⟩

/-- The smaller-gamma parent-prefix producer controls its depth-14 return by
the unpatched safe endpoint used by the scalar upper bounds. The endpoint table
entry is the distinct old-parent certificate; the `10⁻⁵` reserve is retained
in `safeDepth14EndpointCap`. -/
theorem scalar_unpatched_parent14_cap_of_smaller_gamma
    (M : ABKModel 2) (m : ℤ)
    (hsource : NativeSourceSmallerGammaBounds M m) :
    nativeCompletedSourceMean M m 14 ≤
      ENNReal.ofReal (theta M * safeDepth14EndpointCap) := by
  have hparent := hsource.parent (⟨13, by omega⟩ : Fin 16)
  have hindex : nativeBoundaryParentCaps.getD 14 0 = nativeEndpointParent014Cap := by
    norm_num [nativeBoundaryParentCaps, nativeEndpointParent014Cap]
  have hcap : (nativeEndpointParent014Cap : ℝ) ≤ safeDepth14EndpointCap := by
    norm_num [nativeEndpointParent014Cap, safeDepth14EndpointCap]
  change nativeCompletedSourceMean M m 14 ≤
    ENNReal.ofReal (theta M * ((nativeBoundaryParentCaps.getD 14 0 : ℚ) : ℝ)) at hparent
  rw [hindex] at hparent
  have hscale : theta M * (nativeEndpointParent014Cap : ℝ) ≤
      theta M * safeDepth14EndpointCap :=
    mul_le_mul_of_nonneg_left hcap (ASDExplicitGamma.Cold.cold_theta_pos M).le
  exact hparent.trans (ENNReal.ofReal_le_ofReal hscale)

/-- The endpoint corollary from the exact
smaller-gamma conclusion. This exposes the OLD scalar rows and unpatched
depth-14 parent cap consumed by the upper trial. -/
theorem scalar_source_endpoint_corollary_of_smaller_gamma
    (M : ABKModel 2) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hsource : NativeSourceSmallerGammaBounds M m) :
    ordinaryMean M m ≤ ENNReal.ofReal (3 / 50 : ℝ) ∧
      nativeCompletedSourceMean M m 4 ≤
        ENNReal.ofReal (sourceMeanEndpointCaps (⟨4, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceMean M m 5 ≤
        ENNReal.ofReal (sourceMeanEndpointCaps (⟨5, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceWeak M m 5 ≤
        ENNReal.ofReal (weakSourceEndpointCaps (⟨5, by omega⟩ : Fin 6)) ∧
      nativeCompletedSourceMean M m 14 ≤ ENNReal.ofReal safeDepth14EndpointCap := by
  have hold := scalar_old_endpoint_rows_of_smaller_gamma M m hγ hsource
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
    exact hp14θ.trans (ENNReal.ofReal_le_ofReal hscale)
  exact ⟨hold.1, hold.2.1, hold.2.2.1, hold.2.2.2, hp14⟩

end ASDExplicitGamma.Scalar
