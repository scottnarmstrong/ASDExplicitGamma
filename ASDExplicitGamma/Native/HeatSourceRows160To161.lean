module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap160Inputs
public import ASDExplicitGamma.Numerics.Native.Gap161Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap160_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap160System
    let c := nativeIndividualRow 160 (k+1) (nativeOld 160)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 160 = nativeGap160Old := by
    unfold nativeOld
    rw [nativeGap160Raw_formula]
    exact nativeGap160Old_formula
  rw [ho]
  have hz : nativeGap160Scale ≠ 0 := by norm_num [nativeGap160Scale]
  have hs := native_individual_scaled_source_row 160 k nativeGap160Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap160Scale hz hk
  dsimp only at hs
  rw [nativeGap160Coefficients_formula, nativeGap160System_formula] at hs
  exact hs

theorem native_gap161_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap161System
    let c := nativeIndividualRow 161 (k+1) (nativeOld 161)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 161 = nativeGap161Old := by
    unfold nativeOld
    rw [nativeGap161Raw_formula]
    exact nativeGap161Old_formula
  rw [ho]
  have hz : nativeGap161Scale ≠ 0 := by norm_num [nativeGap161Scale]
  have hs := native_individual_scaled_source_row 161 k nativeGap161Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap161Scale hz hk
  dsimp only at hs
  rw [nativeGap161Coefficients_formula, nativeGap161System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
