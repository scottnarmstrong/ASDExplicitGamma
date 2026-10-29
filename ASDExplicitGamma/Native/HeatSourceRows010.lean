module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap010Inputs

/-! Exact degree rows for the configured individual source system. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap010_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap010System
    let c := nativeIndividualRow 10 (k+1) (nativeOld 10)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 10 = nativeGap010Old := by
    unfold nativeOld
    rw [nativeGap010Raw_formula]
    exact nativeGap010Old_formula
  rw [ho]
  have hz : nativeGap010Scale ≠ 0 := by norm_num [nativeGap010Scale]
  have hs := native_individual_scaled_source_row 10 k nativeGap010Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap010Scale hz hk
  dsimp only at hs
  rw [nativeGap010Coefficients_formula, nativeGap010System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
