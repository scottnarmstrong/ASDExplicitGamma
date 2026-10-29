module

public import ASDExplicitGamma.Native.ReturnsFinalTheta

/-! NA-STEP: the target-`N` native component update, unpacked from NA-THETA-SCALING. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Algsuperdiff.Section3
open scoped ENNReal

/-- NA-STEP: from the native states at the labels below `N`, the four native components at `N`
satisfy the carried `θ`-scaled caps. -/
theorem nativeStep_node (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    strong20 M N ≤ ENNReal.ofReal ((2379 / 2500) * theta M) ∧
      root20 M N ≤ ENNReal.ofReal ((2013 / 10000) * theta M) ∧
      buffer40History M N ≤ ENNReal.ofReal ((61 / 10) * theta M) ∧
      bufferMean M N ≤ ENNReal.ofReal ((8 / 25) * theta M) := by
  obtain ⟨_, _, _, _, a, b, c, d⟩ := nativeThetaScaling_node M h hM hg N hN
  exact ⟨a, b, c, d⟩

end ASDExplicitGamma.Native
