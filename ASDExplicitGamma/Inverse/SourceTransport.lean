module

public import ASDExplicitGamma.Inverse.SourceInterfaceTransport
public import ASDExplicitGamma.Inverse.SourceRows

/-! IN-SOURCE-TRANSPORT instantiated from the proved source-row node. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Algsuperdiff.Section3
open ASDExplicitGamma.Native
open scoped ENNReal

/-- Actual completed-law one-shell source transport in the OLD true frame.
The panel uses the model coefficient `M.nu`; its endpoint rows are supplied
by the preceding source-row theorem. -/
theorem in_source_transport
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) :
    (∀ r : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      inSourceMeanActual M m r t ≤
        inSourceMeanActual M m r 0 + t * inSourceMeanSlopeActual M h m r) ∧
      (∀ r : ℕ,
        inSourceMeanActual M m r 0 = (nativeCompletedSourceMean M m r).toReal) ∧
      nativeCompletedSourceMean M m 5 ≤
        ENNReal.ofReal (theta M * (inSourceA5 : ℝ)) ∧
      nativeCompletedSourceWeak M m 5 ≤
        ENNReal.ofReal (theta M * (inSourceXi5Pre : ℝ)) := by
  have hSmall : NativeSourceSmallerGammaBounds M m :=
    native_source_smaller_gamma M h hM hg N hpast m hm
  have hRows := in_source_rows M h hM hg N hpast m hm
  have hTransport := in_source_transport_source M h hM m hSmall
  exact ⟨hTransport.1, hTransport.2.1, hRows.2.2.1, hRows.2.2.2.1⟩

end ASDExplicitGamma.Inverse
