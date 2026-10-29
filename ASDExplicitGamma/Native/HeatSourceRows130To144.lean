module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap130Inputs
public import ASDExplicitGamma.Numerics.Native.Gap131Inputs
public import ASDExplicitGamma.Numerics.Native.Gap132Inputs
public import ASDExplicitGamma.Numerics.Native.Gap133Inputs
public import ASDExplicitGamma.Numerics.Native.Gap134Inputs
public import ASDExplicitGamma.Numerics.Native.Gap135Inputs
public import ASDExplicitGamma.Numerics.Native.Gap136Inputs
public import ASDExplicitGamma.Numerics.Native.Gap137Inputs
public import ASDExplicitGamma.Numerics.Native.Gap138Inputs
public import ASDExplicitGamma.Numerics.Native.Gap139Inputs
public import ASDExplicitGamma.Numerics.Native.Gap140Inputs
public import ASDExplicitGamma.Numerics.Native.Gap141Inputs
public import ASDExplicitGamma.Numerics.Native.Gap142Inputs
public import ASDExplicitGamma.Numerics.Native.Gap143Inputs
public import ASDExplicitGamma.Numerics.Native.Gap144Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap130_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap130System
    let c := nativeIndividualRow 130 (k+1) (nativeOld 130)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 130 = nativeGap130Old := by
    unfold nativeOld
    rw [nativeGap130Raw_formula]
    exact nativeGap130Old_formula
  rw [ho]
  have hz : nativeGap130Scale ≠ 0 := by norm_num [nativeGap130Scale]
  have hs := native_individual_scaled_source_row 130 k nativeGap130Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap130Scale hz hk
  dsimp only at hs
  rw [nativeGap130Coefficients_formula, nativeGap130System_formula] at hs
  exact hs

theorem native_gap131_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap131System
    let c := nativeIndividualRow 131 (k+1) (nativeOld 131)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 131 = nativeGap131Old := by
    unfold nativeOld
    rw [nativeGap131Raw_formula]
    exact nativeGap131Old_formula
  rw [ho]
  have hz : nativeGap131Scale ≠ 0 := by norm_num [nativeGap131Scale]
  have hs := native_individual_scaled_source_row 131 k nativeGap131Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap131Scale hz hk
  dsimp only at hs
  rw [nativeGap131Coefficients_formula, nativeGap131System_formula] at hs
  exact hs

theorem native_gap132_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap132System
    let c := nativeIndividualRow 132 (k+1) (nativeOld 132)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 132 = nativeGap132Old := by
    unfold nativeOld
    rw [nativeGap132Raw_formula]
    exact nativeGap132Old_formula
  rw [ho]
  have hz : nativeGap132Scale ≠ 0 := by norm_num [nativeGap132Scale]
  have hs := native_individual_scaled_source_row 132 k nativeGap132Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap132Scale hz hk
  dsimp only at hs
  rw [nativeGap132Coefficients_formula, nativeGap132System_formula] at hs
  exact hs

theorem native_gap133_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap133System
    let c := nativeIndividualRow 133 (k+1) (nativeOld 133)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 133 = nativeGap133Old := by
    unfold nativeOld
    rw [nativeGap133Raw_formula]
    exact nativeGap133Old_formula
  rw [ho]
  have hz : nativeGap133Scale ≠ 0 := by norm_num [nativeGap133Scale]
  have hs := native_individual_scaled_source_row 133 k nativeGap133Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap133Scale hz hk
  dsimp only at hs
  rw [nativeGap133Coefficients_formula, nativeGap133System_formula] at hs
  exact hs

theorem native_gap134_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap134System
    let c := nativeIndividualRow 134 (k+1) (nativeOld 134)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 134 = nativeGap134Old := by
    unfold nativeOld
    rw [nativeGap134Raw_formula]
    exact nativeGap134Old_formula
  rw [ho]
  have hz : nativeGap134Scale ≠ 0 := by norm_num [nativeGap134Scale]
  have hs := native_individual_scaled_source_row 134 k nativeGap134Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap134Scale hz hk
  dsimp only at hs
  rw [nativeGap134Coefficients_formula, nativeGap134System_formula] at hs
  exact hs

theorem native_gap135_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap135System
    let c := nativeIndividualRow 135 (k+1) (nativeOld 135)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 135 = nativeGap135Old := by
    unfold nativeOld
    rw [nativeGap135Raw_formula]
    exact nativeGap135Old_formula
  rw [ho]
  have hz : nativeGap135Scale ≠ 0 := by norm_num [nativeGap135Scale]
  have hs := native_individual_scaled_source_row 135 k nativeGap135Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap135Scale hz hk
  dsimp only at hs
  rw [nativeGap135Coefficients_formula, nativeGap135System_formula] at hs
  exact hs

theorem native_gap136_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap136System
    let c := nativeIndividualRow 136 (k+1) (nativeOld 136)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 136 = nativeGap136Old := by
    unfold nativeOld
    rw [nativeGap136Raw_formula]
    exact nativeGap136Old_formula
  rw [ho]
  have hz : nativeGap136Scale ≠ 0 := by norm_num [nativeGap136Scale]
  have hs := native_individual_scaled_source_row 136 k nativeGap136Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap136Scale hz hk
  dsimp only at hs
  rw [nativeGap136Coefficients_formula, nativeGap136System_formula] at hs
  exact hs

theorem native_gap137_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap137System
    let c := nativeIndividualRow 137 (k+1) (nativeOld 137)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 137 = nativeGap137Old := by
    unfold nativeOld
    rw [nativeGap137Raw_formula]
    exact nativeGap137Old_formula
  rw [ho]
  have hz : nativeGap137Scale ≠ 0 := by norm_num [nativeGap137Scale]
  have hs := native_individual_scaled_source_row 137 k nativeGap137Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap137Scale hz hk
  dsimp only at hs
  rw [nativeGap137Coefficients_formula, nativeGap137System_formula] at hs
  exact hs

theorem native_gap138_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap138System
    let c := nativeIndividualRow 138 (k+1) (nativeOld 138)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 138 = nativeGap138Old := by
    unfold nativeOld
    rw [nativeGap138Raw_formula]
    exact nativeGap138Old_formula
  rw [ho]
  have hz : nativeGap138Scale ≠ 0 := by norm_num [nativeGap138Scale]
  have hs := native_individual_scaled_source_row 138 k nativeGap138Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap138Scale hz hk
  dsimp only at hs
  rw [nativeGap138Coefficients_formula, nativeGap138System_formula] at hs
  exact hs

theorem native_gap139_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap139System
    let c := nativeIndividualRow 139 (k+1) (nativeOld 139)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 139 = nativeGap139Old := by
    unfold nativeOld
    rw [nativeGap139Raw_formula]
    exact nativeGap139Old_formula
  rw [ho]
  have hz : nativeGap139Scale ≠ 0 := by norm_num [nativeGap139Scale]
  have hs := native_individual_scaled_source_row 139 k nativeGap139Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap139Scale hz hk
  dsimp only at hs
  rw [nativeGap139Coefficients_formula, nativeGap139System_formula] at hs
  exact hs

theorem native_gap140_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap140System
    let c := nativeIndividualRow 140 (k+1) (nativeOld 140)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 140 = nativeGap140Old := by
    unfold nativeOld
    rw [nativeGap140Raw_formula]
    exact nativeGap140Old_formula
  rw [ho]
  have hz : nativeGap140Scale ≠ 0 := by norm_num [nativeGap140Scale]
  have hs := native_individual_scaled_source_row 140 k nativeGap140Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap140Scale hz hk
  dsimp only at hs
  rw [nativeGap140Coefficients_formula, nativeGap140System_formula] at hs
  exact hs

theorem native_gap141_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap141System
    let c := nativeIndividualRow 141 (k+1) (nativeOld 141)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 141 = nativeGap141Old := by
    unfold nativeOld
    rw [nativeGap141Raw_formula]
    exact nativeGap141Old_formula
  rw [ho]
  have hz : nativeGap141Scale ≠ 0 := by norm_num [nativeGap141Scale]
  have hs := native_individual_scaled_source_row 141 k nativeGap141Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap141Scale hz hk
  dsimp only at hs
  rw [nativeGap141Coefficients_formula, nativeGap141System_formula] at hs
  exact hs

theorem native_gap142_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap142System
    let c := nativeIndividualRow 142 (k+1) (nativeOld 142)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 142 = nativeGap142Old := by
    unfold nativeOld
    rw [nativeGap142Raw_formula]
    exact nativeGap142Old_formula
  rw [ho]
  have hz : nativeGap142Scale ≠ 0 := by norm_num [nativeGap142Scale]
  have hs := native_individual_scaled_source_row 142 k nativeGap142Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap142Scale hz hk
  dsimp only at hs
  rw [nativeGap142Coefficients_formula, nativeGap142System_formula] at hs
  exact hs

theorem native_gap143_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap143System
    let c := nativeIndividualRow 143 (k+1) (nativeOld 143)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 143 = nativeGap143Old := by
    unfold nativeOld
    rw [nativeGap143Raw_formula]
    exact nativeGap143Old_formula
  rw [ho]
  have hz : nativeGap143Scale ≠ 0 := by norm_num [nativeGap143Scale]
  have hs := native_individual_scaled_source_row 143 k nativeGap143Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap143Scale hz hk
  dsimp only at hs
  rw [nativeGap143Coefficients_formula, nativeGap143System_formula] at hs
  exact hs

theorem native_gap144_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap144System
    let c := nativeIndividualRow 144 (k+1) (nativeOld 144)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 144 = nativeGap144Old := by
    unfold nativeOld
    rw [nativeGap144Raw_formula]
    exact nativeGap144Old_formula
  rw [ho]
  have hz : nativeGap144Scale ≠ 0 := by norm_num [nativeGap144Scale]
  have hs := native_individual_scaled_source_row 144 k nativeGap144Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap144Scale hz hk
  dsimp only at hs
  rw [nativeGap144Coefficients_formula, nativeGap144System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
