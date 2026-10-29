module

public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Native.SourceRowsSmallerGamma
public import ASDExplicitGamma.Native.ParentPrefix
public import ASDExplicitGamma.Native.SmallerGammaWeak

/-! Conditional target-N native return adapter over the exact
source-smaller-gamma conclusions and the theta-scaled return contract. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Algsuperdiff.Section3
open scoped ENNReal

/-- The exact eight-coordinate output for
`nativeHeatReturns_theta_scaling`: four strict numerical return estimates
followed by the four frozen carried caps. -/
def NativeThetaScaledReturns (M : ABKModel 2) (N : ℤ) : Prop :=
  strong20 M N < ENNReal.ofReal (9515063 / 10^7 * theta M) ∧
  root20 M N < ENNReal.ofReal (2012545 / 10^7 * theta M) ∧
  buffer40History M N < ENNReal.ofReal (5856633 / 10^6 * theta M) ∧
  bufferMean M N < ENNReal.ofReal (317279 / 10^6 * theta M) ∧
  strong20 M N ≤ ENNReal.ofReal (2379 / 2500 * theta M) ∧
  root20 M N ≤ ENNReal.ofReal (2013 / 10000 * theta M) ∧
  buffer40History M N ≤ ENNReal.ofReal (61 / 10 * theta M) ∧
  bufferMean M N ≤ ENNReal.ofReal (8 / 25 * theta M)

/-- The four strict theta-scaled return enclosures imply the four carried
caps. The only input beyond those return estimates is the model's
nonnegative scale factor. -/
theorem native_theta_scaled_carried_caps_of_sharp_returns
    (M : ABKModel 2) (N : ℤ)
    (hθ : 0 ≤ theta M)
    (hstrong : strong20 M N < ENNReal.ofReal (9515063 / 10^7 * theta M))
    (hroot : root20 M N < ENNReal.ofReal (2012545 / 10^7 * theta M))
    (hhistory : buffer40History M N < ENNReal.ofReal (5856633 / 10^6 * theta M))
    (hmean : bufferMean M N < ENNReal.ofReal (317279 / 10^6 * theta M)) :
    strong20 M N ≤ ENNReal.ofReal (2379 / 2500 * theta M) ∧
      root20 M N ≤ ENNReal.ofReal (2013 / 10000 * theta M) ∧
      buffer40History M N ≤ ENNReal.ofReal (61 / 10 * theta M) ∧
      bufferMean M N ≤ ENNReal.ofReal (8 / 25 * theta M) := by
  have hs : (9515063 / 10^7 : ℝ) ≤ 2379 / 2500 := by norm_num
  have hr : (2012545 / 10^7 : ℝ) ≤ 2013 / 10000 := by norm_num
  have hh : (5856633 / 10^6 : ℝ) ≤ 61 / 10 := by norm_num
  have hm : (317279 / 10^6 : ℝ) ≤ 8 / 25 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hstrong.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hs hθ))).le
  · exact (hroot.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hr hθ))).le
  · exact (hhistory.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hh hθ))).le
  · exact (hmean.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hm hθ))).le

/-- Extract the four carried native caps from the exact NA-THETA-SCALING
output. -/
theorem native_step_of_named_producer_outputs
    (M : ABKModel 2) (N : ℤ)
    (hscale : NativeThetaScaledReturns M N) :
    strong20 M N ≤ ENNReal.ofReal (2379 / 2500 * theta M) ∧
      root20 M N ≤ ENNReal.ofReal (2013 / 10000 * theta M) ∧
      buffer40History M N ≤ ENNReal.ofReal (61 / 10 * theta M) ∧
      bufferMean M N ≤ ENNReal.ofReal (8 / 25 * theta M) := by
  rcases hscale with ⟨hstrong, hroot, hhistory, hmean, _, _, _, _⟩
  exact native_theta_scaled_carried_caps_of_sharp_returns M N
    (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero]))
    hstrong hroot hhistory hmean

end ASDExplicitGamma.Native
