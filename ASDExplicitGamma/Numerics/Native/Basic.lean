module

public import ASDExplicitGamma.Numerics.Inverse.RealBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! NU-NA-HISTORY-CONSTANTS, NU-NA-THETA-EXPONENTS and NU-NA-MOLECULAR-STARTUP.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeGamma : ℚ := 17/50000
def nativeA : ℚ := 3/50
def nativeRoot : ℚ := 11
def nativeAvg : ℚ := 1+50*nativeRoot/3^9
def nativeC0 : ℚ := 241/1000
def nativeHistoryRatio : ℚ := 84807022/10^8
def nativeQstar : ℚ := 109585425260485981721911610633/1562500000000000000000000000000

theorem native_history_constants :
    nativeAvg = 20233/19683 ∧ (1-nativeC0)^4 < (1/3 : ℚ) ∧
    (1/27 : ℚ) < nativeHistoryRatio^20 ∧ 0 < nativeHistoryRatio ∧ nativeHistoryRatio < 1 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Native
