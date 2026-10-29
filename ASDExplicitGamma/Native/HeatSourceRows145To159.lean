module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap145Inputs
public import ASDExplicitGamma.Numerics.Native.Gap146Inputs
public import ASDExplicitGamma.Numerics.Native.Gap147Inputs
public import ASDExplicitGamma.Numerics.Native.Gap148Inputs
public import ASDExplicitGamma.Numerics.Native.Gap149Inputs
public import ASDExplicitGamma.Numerics.Native.Gap150Inputs
public import ASDExplicitGamma.Numerics.Native.Gap151Inputs
public import ASDExplicitGamma.Numerics.Native.Gap152Inputs
public import ASDExplicitGamma.Numerics.Native.Gap153Inputs
public import ASDExplicitGamma.Numerics.Native.Gap154Inputs
public import ASDExplicitGamma.Numerics.Native.Gap155Inputs
public import ASDExplicitGamma.Numerics.Native.Gap156Inputs
public import ASDExplicitGamma.Numerics.Native.Gap157Inputs
public import ASDExplicitGamma.Numerics.Native.Gap158Inputs
public import ASDExplicitGamma.Numerics.Native.Gap159Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap145_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap145System
    let c := nativeIndividualRow 145 (k+1) (nativeOld 145)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 145 = nativeGap145Old := by
    unfold nativeOld
    rw [nativeGap145Raw_formula]
    exact nativeGap145Old_formula
  rw [ho]
  have hz : nativeGap145Scale ≠ 0 := by norm_num [nativeGap145Scale]
  have hs := native_individual_scaled_source_row 145 k nativeGap145Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap145Scale hz hk
  dsimp only at hs
  rw [nativeGap145Coefficients_formula, nativeGap145System_formula] at hs
  exact hs

theorem native_gap146_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap146System
    let c := nativeIndividualRow 146 (k+1) (nativeOld 146)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 146 = nativeGap146Old := by
    unfold nativeOld
    rw [nativeGap146Raw_formula]
    exact nativeGap146Old_formula
  rw [ho]
  have hz : nativeGap146Scale ≠ 0 := by norm_num [nativeGap146Scale]
  have hs := native_individual_scaled_source_row 146 k nativeGap146Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap146Scale hz hk
  dsimp only at hs
  rw [nativeGap146Coefficients_formula, nativeGap146System_formula] at hs
  exact hs

theorem native_gap147_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap147System
    let c := nativeIndividualRow 147 (k+1) (nativeOld 147)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 147 = nativeGap147Old := by
    unfold nativeOld
    rw [nativeGap147Raw_formula]
    exact nativeGap147Old_formula
  rw [ho]
  have hz : nativeGap147Scale ≠ 0 := by norm_num [nativeGap147Scale]
  have hs := native_individual_scaled_source_row 147 k nativeGap147Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap147Scale hz hk
  dsimp only at hs
  rw [nativeGap147Coefficients_formula, nativeGap147System_formula] at hs
  exact hs

theorem native_gap148_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap148System
    let c := nativeIndividualRow 148 (k+1) (nativeOld 148)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 148 = nativeGap148Old := by
    unfold nativeOld
    rw [nativeGap148Raw_formula]
    exact nativeGap148Old_formula
  rw [ho]
  have hz : nativeGap148Scale ≠ 0 := by norm_num [nativeGap148Scale]
  have hs := native_individual_scaled_source_row 148 k nativeGap148Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap148Scale hz hk
  dsimp only at hs
  rw [nativeGap148Coefficients_formula, nativeGap148System_formula] at hs
  exact hs

theorem native_gap149_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap149System
    let c := nativeIndividualRow 149 (k+1) (nativeOld 149)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 149 = nativeGap149Old := by
    unfold nativeOld
    rw [nativeGap149Raw_formula]
    exact nativeGap149Old_formula
  rw [ho]
  have hz : nativeGap149Scale ≠ 0 := by norm_num [nativeGap149Scale]
  have hs := native_individual_scaled_source_row 149 k nativeGap149Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap149Scale hz hk
  dsimp only at hs
  rw [nativeGap149Coefficients_formula, nativeGap149System_formula] at hs
  exact hs

theorem native_gap150_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap150System
    let c := nativeIndividualRow 150 (k+1) (nativeOld 150)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 150 = nativeGap150Old := by
    unfold nativeOld
    rw [nativeGap150Raw_formula]
    exact nativeGap150Old_formula
  rw [ho]
  have hz : nativeGap150Scale ≠ 0 := by norm_num [nativeGap150Scale]
  have hs := native_individual_scaled_source_row 150 k nativeGap150Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap150Scale hz hk
  dsimp only at hs
  rw [nativeGap150Coefficients_formula, nativeGap150System_formula] at hs
  exact hs

theorem native_gap151_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap151System
    let c := nativeIndividualRow 151 (k+1) (nativeOld 151)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 151 = nativeGap151Old := by
    unfold nativeOld
    rw [nativeGap151Raw_formula]
    exact nativeGap151Old_formula
  rw [ho]
  have hz : nativeGap151Scale ≠ 0 := by norm_num [nativeGap151Scale]
  have hs := native_individual_scaled_source_row 151 k nativeGap151Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap151Scale hz hk
  dsimp only at hs
  rw [nativeGap151Coefficients_formula, nativeGap151System_formula] at hs
  exact hs

theorem native_gap152_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap152System
    let c := nativeIndividualRow 152 (k+1) (nativeOld 152)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 152 = nativeGap152Old := by
    unfold nativeOld
    rw [nativeGap152Raw_formula]
    exact nativeGap152Old_formula
  rw [ho]
  have hz : nativeGap152Scale ≠ 0 := by norm_num [nativeGap152Scale]
  have hs := native_individual_scaled_source_row 152 k nativeGap152Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap152Scale hz hk
  dsimp only at hs
  rw [nativeGap152Coefficients_formula, nativeGap152System_formula] at hs
  exact hs

theorem native_gap153_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap153System
    let c := nativeIndividualRow 153 (k+1) (nativeOld 153)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 153 = nativeGap153Old := by
    unfold nativeOld
    rw [nativeGap153Raw_formula]
    exact nativeGap153Old_formula
  rw [ho]
  have hz : nativeGap153Scale ≠ 0 := by norm_num [nativeGap153Scale]
  have hs := native_individual_scaled_source_row 153 k nativeGap153Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap153Scale hz hk
  dsimp only at hs
  rw [nativeGap153Coefficients_formula, nativeGap153System_formula] at hs
  exact hs

theorem native_gap154_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap154System
    let c := nativeIndividualRow 154 (k+1) (nativeOld 154)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 154 = nativeGap154Old := by
    unfold nativeOld
    rw [nativeGap154Raw_formula]
    exact nativeGap154Old_formula
  rw [ho]
  have hz : nativeGap154Scale ≠ 0 := by norm_num [nativeGap154Scale]
  have hs := native_individual_scaled_source_row 154 k nativeGap154Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap154Scale hz hk
  dsimp only at hs
  rw [nativeGap154Coefficients_formula, nativeGap154System_formula] at hs
  exact hs

theorem native_gap155_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap155System
    let c := nativeIndividualRow 155 (k+1) (nativeOld 155)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 155 = nativeGap155Old := by
    unfold nativeOld
    rw [nativeGap155Raw_formula]
    exact nativeGap155Old_formula
  rw [ho]
  have hz : nativeGap155Scale ≠ 0 := by norm_num [nativeGap155Scale]
  have hs := native_individual_scaled_source_row 155 k nativeGap155Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap155Scale hz hk
  dsimp only at hs
  rw [nativeGap155Coefficients_formula, nativeGap155System_formula] at hs
  exact hs

theorem native_gap156_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap156System
    let c := nativeIndividualRow 156 (k+1) (nativeOld 156)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 156 = nativeGap156Old := by
    unfold nativeOld
    rw [nativeGap156Raw_formula]
    exact nativeGap156Old_formula
  rw [ho]
  have hz : nativeGap156Scale ≠ 0 := by norm_num [nativeGap156Scale]
  have hs := native_individual_scaled_source_row 156 k nativeGap156Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap156Scale hz hk
  dsimp only at hs
  rw [nativeGap156Coefficients_formula, nativeGap156System_formula] at hs
  exact hs

theorem native_gap157_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap157System
    let c := nativeIndividualRow 157 (k+1) (nativeOld 157)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 157 = nativeGap157Old := by
    unfold nativeOld
    rw [nativeGap157Raw_formula]
    exact nativeGap157Old_formula
  rw [ho]
  have hz : nativeGap157Scale ≠ 0 := by norm_num [nativeGap157Scale]
  have hs := native_individual_scaled_source_row 157 k nativeGap157Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap157Scale hz hk
  dsimp only at hs
  rw [nativeGap157Coefficients_formula, nativeGap157System_formula] at hs
  exact hs

theorem native_gap158_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap158System
    let c := nativeIndividualRow 158 (k+1) (nativeOld 158)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 158 = nativeGap158Old := by
    unfold nativeOld
    rw [nativeGap158Raw_formula]
    exact nativeGap158Old_formula
  rw [ho]
  have hz : nativeGap158Scale ≠ 0 := by norm_num [nativeGap158Scale]
  have hs := native_individual_scaled_source_row 158 k nativeGap158Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap158Scale hz hk
  dsimp only at hs
  rw [nativeGap158Coefficients_formula, nativeGap158System_formula] at hs
  exact hs

theorem native_gap159_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap159System
    let c := nativeIndividualRow 159 (k+1) (nativeOld 159)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 159 = nativeGap159Old := by
    unfold nativeOld
    rw [nativeGap159Raw_formula]
    exact nativeGap159Old_formula
  rw [ho]
  have hz : nativeGap159Scale ≠ 0 := by norm_num [nativeGap159Scale]
  have hs := native_individual_scaled_source_row 159 k nativeGap159Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap159Scale hz hk
  dsimp only at hs
  rw [nativeGap159Coefficients_formula, nativeGap159System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
