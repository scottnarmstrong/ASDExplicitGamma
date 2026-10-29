module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap040Inputs
public import ASDExplicitGamma.Numerics.Native.Gap041Inputs
public import ASDExplicitGamma.Numerics.Native.Gap042Inputs
public import ASDExplicitGamma.Numerics.Native.Gap043Inputs
public import ASDExplicitGamma.Numerics.Native.Gap044Inputs
public import ASDExplicitGamma.Numerics.Native.Gap045Inputs
public import ASDExplicitGamma.Numerics.Native.Gap046Inputs
public import ASDExplicitGamma.Numerics.Native.Gap047Inputs
public import ASDExplicitGamma.Numerics.Native.Gap048Inputs
public import ASDExplicitGamma.Numerics.Native.Gap049Inputs
public import ASDExplicitGamma.Numerics.Native.Gap050Inputs
public import ASDExplicitGamma.Numerics.Native.Gap051Inputs
public import ASDExplicitGamma.Numerics.Native.Gap052Inputs
public import ASDExplicitGamma.Numerics.Native.Gap053Inputs
public import ASDExplicitGamma.Numerics.Native.Gap054Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap040_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap040System
    let c := nativeIndividualRow 40 (k+1) (nativeOld 40)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 40 = nativeGap040Old := by
    unfold nativeOld
    rw [nativeGap040Raw_formula]
    exact nativeGap040Old_formula
  rw [ho]
  have hz : nativeGap040Scale ≠ 0 := by norm_num [nativeGap040Scale]
  have hs := native_individual_scaled_source_row 40 k nativeGap040Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap040Scale hz hk
  dsimp only at hs
  rw [nativeGap040Coefficients_formula, nativeGap040System_formula] at hs
  exact hs

theorem native_gap041_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap041System
    let c := nativeIndividualRow 41 (k+1) (nativeOld 41)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 41 = nativeGap041Old := by
    unfold nativeOld
    rw [nativeGap041Raw_formula]
    exact nativeGap041Old_formula
  rw [ho]
  have hz : nativeGap041Scale ≠ 0 := by norm_num [nativeGap041Scale]
  have hs := native_individual_scaled_source_row 41 k nativeGap041Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap041Scale hz hk
  dsimp only at hs
  rw [nativeGap041Coefficients_formula, nativeGap041System_formula] at hs
  exact hs

theorem native_gap042_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap042System
    let c := nativeIndividualRow 42 (k+1) (nativeOld 42)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 42 = nativeGap042Old := by
    unfold nativeOld
    rw [nativeGap042Raw_formula]
    exact nativeGap042Old_formula
  rw [ho]
  have hz : nativeGap042Scale ≠ 0 := by norm_num [nativeGap042Scale]
  have hs := native_individual_scaled_source_row 42 k nativeGap042Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap042Scale hz hk
  dsimp only at hs
  rw [nativeGap042Coefficients_formula, nativeGap042System_formula] at hs
  exact hs

theorem native_gap043_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap043System
    let c := nativeIndividualRow 43 (k+1) (nativeOld 43)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 43 = nativeGap043Old := by
    unfold nativeOld
    rw [nativeGap043Raw_formula]
    exact nativeGap043Old_formula
  rw [ho]
  have hz : nativeGap043Scale ≠ 0 := by norm_num [nativeGap043Scale]
  have hs := native_individual_scaled_source_row 43 k nativeGap043Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap043Scale hz hk
  dsimp only at hs
  rw [nativeGap043Coefficients_formula, nativeGap043System_formula] at hs
  exact hs

theorem native_gap044_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap044System
    let c := nativeIndividualRow 44 (k+1) (nativeOld 44)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 44 = nativeGap044Old := by
    unfold nativeOld
    rw [nativeGap044Raw_formula]
    exact nativeGap044Old_formula
  rw [ho]
  have hz : nativeGap044Scale ≠ 0 := by norm_num [nativeGap044Scale]
  have hs := native_individual_scaled_source_row 44 k nativeGap044Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap044Scale hz hk
  dsimp only at hs
  rw [nativeGap044Coefficients_formula, nativeGap044System_formula] at hs
  exact hs

theorem native_gap045_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap045System
    let c := nativeIndividualRow 45 (k+1) (nativeOld 45)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 45 = nativeGap045Old := by
    unfold nativeOld
    rw [nativeGap045Raw_formula]
    exact nativeGap045Old_formula
  rw [ho]
  have hz : nativeGap045Scale ≠ 0 := by norm_num [nativeGap045Scale]
  have hs := native_individual_scaled_source_row 45 k nativeGap045Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap045Scale hz hk
  dsimp only at hs
  rw [nativeGap045Coefficients_formula, nativeGap045System_formula] at hs
  exact hs

theorem native_gap046_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap046System
    let c := nativeIndividualRow 46 (k+1) (nativeOld 46)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 46 = nativeGap046Old := by
    unfold nativeOld
    rw [nativeGap046Raw_formula]
    exact nativeGap046Old_formula
  rw [ho]
  have hz : nativeGap046Scale ≠ 0 := by norm_num [nativeGap046Scale]
  have hs := native_individual_scaled_source_row 46 k nativeGap046Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap046Scale hz hk
  dsimp only at hs
  rw [nativeGap046Coefficients_formula, nativeGap046System_formula] at hs
  exact hs

theorem native_gap047_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap047System
    let c := nativeIndividualRow 47 (k+1) (nativeOld 47)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 47 = nativeGap047Old := by
    unfold nativeOld
    rw [nativeGap047Raw_formula]
    exact nativeGap047Old_formula
  rw [ho]
  have hz : nativeGap047Scale ≠ 0 := by norm_num [nativeGap047Scale]
  have hs := native_individual_scaled_source_row 47 k nativeGap047Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap047Scale hz hk
  dsimp only at hs
  rw [nativeGap047Coefficients_formula, nativeGap047System_formula] at hs
  exact hs

theorem native_gap048_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap048System
    let c := nativeIndividualRow 48 (k+1) (nativeOld 48)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 48 = nativeGap048Old := by
    unfold nativeOld
    rw [nativeGap048Raw_formula]
    exact nativeGap048Old_formula
  rw [ho]
  have hz : nativeGap048Scale ≠ 0 := by norm_num [nativeGap048Scale]
  have hs := native_individual_scaled_source_row 48 k nativeGap048Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap048Scale hz hk
  dsimp only at hs
  rw [nativeGap048Coefficients_formula, nativeGap048System_formula] at hs
  exact hs

theorem native_gap049_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap049System
    let c := nativeIndividualRow 49 (k+1) (nativeOld 49)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 49 = nativeGap049Old := by
    unfold nativeOld
    rw [nativeGap049Raw_formula]
    exact nativeGap049Old_formula
  rw [ho]
  have hz : nativeGap049Scale ≠ 0 := by norm_num [nativeGap049Scale]
  have hs := native_individual_scaled_source_row 49 k nativeGap049Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap049Scale hz hk
  dsimp only at hs
  rw [nativeGap049Coefficients_formula, nativeGap049System_formula] at hs
  exact hs

theorem native_gap050_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap050System
    let c := nativeIndividualRow 50 (k+1) (nativeOld 50)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 50 = nativeGap050Old := by
    unfold nativeOld
    rw [nativeGap050Raw_formula]
    exact nativeGap050Old_formula
  rw [ho]
  have hz : nativeGap050Scale ≠ 0 := by norm_num [nativeGap050Scale]
  have hs := native_individual_scaled_source_row 50 k nativeGap050Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap050Scale hz hk
  dsimp only at hs
  rw [nativeGap050Coefficients_formula, nativeGap050System_formula] at hs
  exact hs

theorem native_gap051_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap051System
    let c := nativeIndividualRow 51 (k+1) (nativeOld 51)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 51 = nativeGap051Old := by
    unfold nativeOld
    rw [nativeGap051Raw_formula]
    exact nativeGap051Old_formula
  rw [ho]
  have hz : nativeGap051Scale ≠ 0 := by norm_num [nativeGap051Scale]
  have hs := native_individual_scaled_source_row 51 k nativeGap051Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap051Scale hz hk
  dsimp only at hs
  rw [nativeGap051Coefficients_formula, nativeGap051System_formula] at hs
  exact hs

theorem native_gap052_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap052System
    let c := nativeIndividualRow 52 (k+1) (nativeOld 52)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 52 = nativeGap052Old := by
    unfold nativeOld
    rw [nativeGap052Raw_formula]
    exact nativeGap052Old_formula
  rw [ho]
  have hz : nativeGap052Scale ≠ 0 := by norm_num [nativeGap052Scale]
  have hs := native_individual_scaled_source_row 52 k nativeGap052Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap052Scale hz hk
  dsimp only at hs
  rw [nativeGap052Coefficients_formula, nativeGap052System_formula] at hs
  exact hs

theorem native_gap053_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap053System
    let c := nativeIndividualRow 53 (k+1) (nativeOld 53)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 53 = nativeGap053Old := by
    unfold nativeOld
    rw [nativeGap053Raw_formula]
    exact nativeGap053Old_formula
  rw [ho]
  have hz : nativeGap053Scale ≠ 0 := by norm_num [nativeGap053Scale]
  have hs := native_individual_scaled_source_row 53 k nativeGap053Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap053Scale hz hk
  dsimp only at hs
  rw [nativeGap053Coefficients_formula, nativeGap053System_formula] at hs
  exact hs

theorem native_gap054_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap054System
    let c := nativeIndividualRow 54 (k+1) (nativeOld 54)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 54 = nativeGap054Old := by
    unfold nativeOld
    rw [nativeGap054Raw_formula]
    exact nativeGap054Old_formula
  rw [ho]
  have hz : nativeGap054Scale ≠ 0 := by norm_num [nativeGap054Scale]
  have hs := native_individual_scaled_source_row 54 k nativeGap054Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap054Scale hz hk
  dsimp only at hs
  rw [nativeGap054Coefficients_formula, nativeGap054System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
