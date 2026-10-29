module

public import ASDExplicitGamma.Native.GenericSourceEndpointActual
public import ASDExplicitGamma.Native.SourceRowsInterface

/-! The smaller-γ source continuation, assembled from the exact producer
conclusions proved separately. The generic producer output is retained alongside
the four target families so downstream consumers can use its complete rows. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal
noncomputable section

/-- Exact bundled output of the generic/refined source-row producer. -/
def NativeGenericSourceRowsConclusion
    (M : ABKModel 2) (m : ℤ) : Prop :=
  (∀ depth : ℕ, 9+depth ≤ 1332 →
    nativeCompletedSourceMean M m depth ≤
      ENNReal.ofReal (theta M * nativeSourceGenericMeanProfile
        (17/50000) 1 (9+depth))) ∧
  (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
    ENNReal.ofReal (theta M * nativeSourceWeakInverseCharge
      (nativeSourceGenericCompleteMeanRow (17/50000) 1 r.val 1285)
      (nativeSourceGenericCompleteWeakRow (17/50000) 1 r.val 1285))) ∧
  (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
    ENNReal.ofReal (theta M * (nativeCompletedPrefixOldMean r : ℝ))) ∧
  (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
    ENNReal.ofReal (theta M * (nativeCompletedPrefixOldXi r : ℝ)))

end
end ASDExplicitGamma.Native
