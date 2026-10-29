module

public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Native.SourceChainRows

/-! IN-SOURCE-ROWS instantiated from the accepted native source producers. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Algsuperdiff.Section3
open ASDExplicitGamma.Native
open scoped ENNReal

/-- The actual completed OLD source-row interface at every source label
strictly below the outer induction target. The two producers supply
the smaller-gamma data and the certified exact six-row source caps. -/
theorem in_source_rows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) :
    ordinaryMean M m ≤ ENNReal.ofReal (theta M * (3 / 50 : ℝ)) ∧
      nativeCompletedSourceMean M m 4 ≤
        ENNReal.ofReal (theta M * (inSourceA4 : ℝ)) ∧
      nativeCompletedSourceMean M m 5 ≤
        ENNReal.ofReal (theta M * (inSourceA5 : ℝ)) ∧
      nativeCompletedSourceWeak M m 5 ≤
        ENNReal.ofReal (theta M * (inSourceXi5Pre : ℝ)) ∧
      nativeCompletedSourceMean M m 0 = ordinaryMean M m := by
  have hSmall : NativeSourceSmallerGammaBounds M m :=
    native_source_smaller_gamma M h hM hg N hpast m hm
  have hRows : NativeSourceRowsBounds M m :=
    native_source_rows M h hM hg N hpast m hm
  have hInterface := in_source_rows_source M m hSmall
  refine ⟨hInterface.1, ?_, ?_, hInterface.2.2.2.1, hInterface.2.2.2.2⟩
  · simpa [inSourceA4] using hRows.mean_four
  · simpa [inSourceA5] using hRows.mean_five

end ASDExplicitGamma.Inverse
