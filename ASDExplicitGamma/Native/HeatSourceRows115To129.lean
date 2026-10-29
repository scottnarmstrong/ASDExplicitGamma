module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap115Inputs
public import ASDExplicitGamma.Numerics.Native.Gap116Inputs
public import ASDExplicitGamma.Numerics.Native.Gap117Inputs
public import ASDExplicitGamma.Numerics.Native.Gap118Inputs
public import ASDExplicitGamma.Numerics.Native.Gap119Inputs
public import ASDExplicitGamma.Numerics.Native.Gap120Inputs
public import ASDExplicitGamma.Numerics.Native.Gap121Inputs
public import ASDExplicitGamma.Numerics.Native.Gap122Inputs
public import ASDExplicitGamma.Numerics.Native.Gap123Inputs
public import ASDExplicitGamma.Numerics.Native.Gap124Inputs
public import ASDExplicitGamma.Numerics.Native.Gap125Inputs
public import ASDExplicitGamma.Numerics.Native.Gap126Inputs
public import ASDExplicitGamma.Numerics.Native.Gap127Inputs
public import ASDExplicitGamma.Numerics.Native.Gap128Inputs
public import ASDExplicitGamma.Numerics.Native.Gap129Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap115_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap115System
    let c := nativeIndividualRow 115 (k+1) (nativeOld 115)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 115 = nativeGap115Old := by
    unfold nativeOld
    rw [nativeGap115Raw_formula]
    exact nativeGap115Old_formula
  rw [ho]
  have hz : nativeGap115Scale ≠ 0 := by norm_num [nativeGap115Scale]
  have hs := native_individual_scaled_source_row 115 k nativeGap115Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap115Scale hz hk
  dsimp only at hs
  rw [nativeGap115Coefficients_formula, nativeGap115System_formula] at hs
  exact hs

theorem native_gap116_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap116System
    let c := nativeIndividualRow 116 (k+1) (nativeOld 116)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 116 = nativeGap116Old := by
    unfold nativeOld
    rw [nativeGap116Raw_formula]
    exact nativeGap116Old_formula
  rw [ho]
  have hz : nativeGap116Scale ≠ 0 := by norm_num [nativeGap116Scale]
  have hs := native_individual_scaled_source_row 116 k nativeGap116Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap116Scale hz hk
  dsimp only at hs
  rw [nativeGap116Coefficients_formula, nativeGap116System_formula] at hs
  exact hs

theorem native_gap117_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap117System
    let c := nativeIndividualRow 117 (k+1) (nativeOld 117)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 117 = nativeGap117Old := by
    unfold nativeOld
    rw [nativeGap117Raw_formula]
    exact nativeGap117Old_formula
  rw [ho]
  have hz : nativeGap117Scale ≠ 0 := by norm_num [nativeGap117Scale]
  have hs := native_individual_scaled_source_row 117 k nativeGap117Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap117Scale hz hk
  dsimp only at hs
  rw [nativeGap117Coefficients_formula, nativeGap117System_formula] at hs
  exact hs

theorem native_gap118_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap118System
    let c := nativeIndividualRow 118 (k+1) (nativeOld 118)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 118 = nativeGap118Old := by
    unfold nativeOld
    rw [nativeGap118Raw_formula]
    exact nativeGap118Old_formula
  rw [ho]
  have hz : nativeGap118Scale ≠ 0 := by norm_num [nativeGap118Scale]
  have hs := native_individual_scaled_source_row 118 k nativeGap118Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap118Scale hz hk
  dsimp only at hs
  rw [nativeGap118Coefficients_formula, nativeGap118System_formula] at hs
  exact hs

theorem native_gap119_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap119System
    let c := nativeIndividualRow 119 (k+1) (nativeOld 119)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 119 = nativeGap119Old := by
    unfold nativeOld
    rw [nativeGap119Raw_formula]
    exact nativeGap119Old_formula
  rw [ho]
  have hz : nativeGap119Scale ≠ 0 := by norm_num [nativeGap119Scale]
  have hs := native_individual_scaled_source_row 119 k nativeGap119Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap119Scale hz hk
  dsimp only at hs
  rw [nativeGap119Coefficients_formula, nativeGap119System_formula] at hs
  exact hs

theorem native_gap120_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap120System
    let c := nativeIndividualRow 120 (k+1) (nativeOld 120)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 120 = nativeGap120Old := by
    unfold nativeOld
    rw [nativeGap120Raw_formula]
    exact nativeGap120Old_formula
  rw [ho]
  have hz : nativeGap120Scale ≠ 0 := by norm_num [nativeGap120Scale]
  have hs := native_individual_scaled_source_row 120 k nativeGap120Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap120Scale hz hk
  dsimp only at hs
  rw [nativeGap120Coefficients_formula, nativeGap120System_formula] at hs
  exact hs

theorem native_gap121_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap121System
    let c := nativeIndividualRow 121 (k+1) (nativeOld 121)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 121 = nativeGap121Old := by
    unfold nativeOld
    rw [nativeGap121Raw_formula]
    exact nativeGap121Old_formula
  rw [ho]
  have hz : nativeGap121Scale ≠ 0 := by norm_num [nativeGap121Scale]
  have hs := native_individual_scaled_source_row 121 k nativeGap121Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap121Scale hz hk
  dsimp only at hs
  rw [nativeGap121Coefficients_formula, nativeGap121System_formula] at hs
  exact hs

theorem native_gap122_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap122System
    let c := nativeIndividualRow 122 (k+1) (nativeOld 122)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 122 = nativeGap122Old := by
    unfold nativeOld
    rw [nativeGap122Raw_formula]
    exact nativeGap122Old_formula
  rw [ho]
  have hz : nativeGap122Scale ≠ 0 := by norm_num [nativeGap122Scale]
  have hs := native_individual_scaled_source_row 122 k nativeGap122Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap122Scale hz hk
  dsimp only at hs
  rw [nativeGap122Coefficients_formula, nativeGap122System_formula] at hs
  exact hs

theorem native_gap123_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap123System
    let c := nativeIndividualRow 123 (k+1) (nativeOld 123)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 123 = nativeGap123Old := by
    unfold nativeOld
    rw [nativeGap123Raw_formula]
    exact nativeGap123Old_formula
  rw [ho]
  have hz : nativeGap123Scale ≠ 0 := by norm_num [nativeGap123Scale]
  have hs := native_individual_scaled_source_row 123 k nativeGap123Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap123Scale hz hk
  dsimp only at hs
  rw [nativeGap123Coefficients_formula, nativeGap123System_formula] at hs
  exact hs

theorem native_gap124_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap124System
    let c := nativeIndividualRow 124 (k+1) (nativeOld 124)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 124 = nativeGap124Old := by
    unfold nativeOld
    rw [nativeGap124Raw_formula]
    exact nativeGap124Old_formula
  rw [ho]
  have hz : nativeGap124Scale ≠ 0 := by norm_num [nativeGap124Scale]
  have hs := native_individual_scaled_source_row 124 k nativeGap124Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap124Scale hz hk
  dsimp only at hs
  rw [nativeGap124Coefficients_formula, nativeGap124System_formula] at hs
  exact hs

theorem native_gap125_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap125System
    let c := nativeIndividualRow 125 (k+1) (nativeOld 125)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 125 = nativeGap125Old := by
    unfold nativeOld
    rw [nativeGap125Raw_formula]
    exact nativeGap125Old_formula
  rw [ho]
  have hz : nativeGap125Scale ≠ 0 := by norm_num [nativeGap125Scale]
  have hs := native_individual_scaled_source_row 125 k nativeGap125Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap125Scale hz hk
  dsimp only at hs
  rw [nativeGap125Coefficients_formula, nativeGap125System_formula] at hs
  exact hs

theorem native_gap126_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap126System
    let c := nativeIndividualRow 126 (k+1) (nativeOld 126)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 126 = nativeGap126Old := by
    unfold nativeOld
    rw [nativeGap126Raw_formula]
    exact nativeGap126Old_formula
  rw [ho]
  have hz : nativeGap126Scale ≠ 0 := by norm_num [nativeGap126Scale]
  have hs := native_individual_scaled_source_row 126 k nativeGap126Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap126Scale hz hk
  dsimp only at hs
  rw [nativeGap126Coefficients_formula, nativeGap126System_formula] at hs
  exact hs

theorem native_gap127_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap127System
    let c := nativeIndividualRow 127 (k+1) (nativeOld 127)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 127 = nativeGap127Old := by
    unfold nativeOld
    rw [nativeGap127Raw_formula]
    exact nativeGap127Old_formula
  rw [ho]
  have hz : nativeGap127Scale ≠ 0 := by norm_num [nativeGap127Scale]
  have hs := native_individual_scaled_source_row 127 k nativeGap127Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap127Scale hz hk
  dsimp only at hs
  rw [nativeGap127Coefficients_formula, nativeGap127System_formula] at hs
  exact hs

theorem native_gap128_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap128System
    let c := nativeIndividualRow 128 (k+1) (nativeOld 128)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 128 = nativeGap128Old := by
    unfold nativeOld
    rw [nativeGap128Raw_formula]
    exact nativeGap128Old_formula
  rw [ho]
  have hz : nativeGap128Scale ≠ 0 := by norm_num [nativeGap128Scale]
  have hs := native_individual_scaled_source_row 128 k nativeGap128Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap128Scale hz hk
  dsimp only at hs
  rw [nativeGap128Coefficients_formula, nativeGap128System_formula] at hs
  exact hs

theorem native_gap129_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap129System
    let c := nativeIndividualRow 129 (k+1) (nativeOld 129)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 129 = nativeGap129Old := by
    unfold nativeOld
    rw [nativeGap129Raw_formula]
    exact nativeGap129Old_formula
  rw [ho]
  have hz : nativeGap129Scale ≠ 0 := by norm_num [nativeGap129Scale]
  have hs := native_individual_scaled_source_row 129 k nativeGap129Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap129Scale hz hk
  dsimp only at hs
  rw [nativeGap129Coefficients_formula, nativeGap129System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
