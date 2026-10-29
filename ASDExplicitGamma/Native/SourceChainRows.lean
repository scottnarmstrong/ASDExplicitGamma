module

public import ASDExplicitGamma.Native.SourceChainSmallerGamma
public import ASDExplicitGamma.Native.SourceRowsSmallerGamma

/-! The exact six-row source interface on the actual completed law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- NA-SOURCE-ROWS: the six exact certified mean and weak caps. The
six-digit displays are available only as corollaries of this conclusion. -/
theorem native_source_rows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (m : ℤ) (hm : m < N) :
    NativeSourceRowsBounds M m :=
  native_source_rows_from_smaller_gamma M m
    (native_source_smaller_gamma M h hM hg N hpast m hm)

end
end ASDExplicitGamma.Native
