module

public import ASDExplicitGamma.Scalar.SourceEndpoint
public import ASDExplicitGamma.Scalar.SourceQ1Adapter
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Native.SourceSmallerGammaInterface

/-! The corrected q1 boundary-charge comparison used by the scalar lower
input bridge. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Main
  ASDExplicitGamma.Inverse
open scoped ENNReal

/-- The exact smaller-gamma source endpoint output consumed by the lower
input bridge. The endpoint row producer is kept separate from the q1 boundary
charge producer. -/
def LowerSourceEndpointConclusion (M : ABKModel 2) (m : ℤ) : Prop :=
  ordinaryMean M m ≤ ENNReal.ofReal (3 / 50 : ℝ) ∧
    nativeCompletedSourceMean M m 4 ≤
      ENNReal.ofReal (sourceMeanEndpointCaps (⟨4, by omega⟩ : Fin 6)) ∧
    nativeCompletedSourceMean M m 5 ≤
      ENNReal.ofReal (sourceMeanEndpointCaps (⟨5, by omega⟩ : Fin 6)) ∧
    nativeCompletedSourceWeak M m 5 ≤
      ENNReal.ofReal (weakSourceEndpointCaps (⟨5, by omega⟩ : Fin 6)) ∧
    nativeCompletedSourceMean M m 14 ≤ ENNReal.ofReal safeDepth14EndpointCap

/-- The named source endpoint contract follows directly from the exact
smaller-gamma helper. -/
theorem lower_source_endpoint_conclusion
    (M : ABKModel 2) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hsource : NativeSourceSmallerGammaBounds M m) :
    LowerSourceEndpointConclusion M m := by
  exact scalar_source_endpoint_corollary_of_smaller_gamma M m hγ hsource

/-- The exact NA-Q1-BOUNDARY-CHARGE conclusion lies below the scalar source
target after consuming the smaller-gamma factor. -/
theorem lower_q1_endpoint_of_boundary_charge
    (M : ABKModel 2) (m : ℤ) (hγ : M.gamma ≤ gammaZero)
    (hq1 : nativeCompletedSourceMean M m 1 ≤
      ENNReal.ofReal (theta M * (nativeBoundaryQ1Sharp : ℝ))) :
    nativeCompletedSourceMean M m 1 ≤ ENNReal.ofReal q1SourceTargetCap := by
  have hθ := ASDExplicitGamma.Cold.cold_theta_le_one M hγ
  have hcapEq : (nativeBoundaryQ1Sharp : ℝ) = q1BoundaryEndpointCap := by
    norm_num [nativeBoundaryQ1Sharp, q1BoundaryEndpointCap]
  have hcap0 : 0 ≤ q1BoundaryEndpointCap := by
    norm_num [q1BoundaryEndpointCap]
  have hscaled : theta M * (nativeBoundaryQ1Sharp : ℝ) ≤
      q1SourceTargetCap := by
    rw [hcapEq]
    calc
      theta M * q1BoundaryEndpointCap ≤ q1BoundaryEndpointCap := by
        calc
          theta M * q1BoundaryEndpointCap ≤
              1 * q1BoundaryEndpointCap :=
            mul_le_mul_of_nonneg_right hθ hcap0
          _ = q1BoundaryEndpointCap := one_mul _
      _ ≤ q1SourceTargetCap :=
        q1BoundaryEndpoint_below_sourceTarget.le
  exact hq1.trans (ENNReal.ofReal_le_ofReal hscaled)

end ASDExplicitGamma.Scalar
