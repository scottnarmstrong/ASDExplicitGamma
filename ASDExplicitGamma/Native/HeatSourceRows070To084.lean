module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap070Inputs
public import ASDExplicitGamma.Numerics.Native.Gap071Inputs
public import ASDExplicitGamma.Numerics.Native.Gap072Inputs
public import ASDExplicitGamma.Numerics.Native.Gap073Inputs
public import ASDExplicitGamma.Numerics.Native.Gap074Inputs
public import ASDExplicitGamma.Numerics.Native.Gap075Inputs
public import ASDExplicitGamma.Numerics.Native.Gap076Inputs
public import ASDExplicitGamma.Numerics.Native.Gap077Inputs
public import ASDExplicitGamma.Numerics.Native.Gap078Inputs
public import ASDExplicitGamma.Numerics.Native.Gap079Inputs
public import ASDExplicitGamma.Numerics.Native.Gap080Inputs
public import ASDExplicitGamma.Numerics.Native.Gap081Inputs
public import ASDExplicitGamma.Numerics.Native.Gap082Inputs
public import ASDExplicitGamma.Numerics.Native.Gap083Inputs
public import ASDExplicitGamma.Numerics.Native.Gap084Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap070_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap070System
    let c := nativeIndividualRow 70 (k+1) (nativeOld 70)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 70 = nativeGap070Old := by
    unfold nativeOld
    rw [nativeGap070Raw_formula]
    exact nativeGap070Old_formula
  rw [ho]
  have hz : nativeGap070Scale ≠ 0 := by norm_num [nativeGap070Scale]
  have hs := native_individual_scaled_source_row 70 k nativeGap070Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap070Scale hz hk
  dsimp only at hs
  rw [nativeGap070Coefficients_formula, nativeGap070System_formula] at hs
  exact hs

theorem native_gap071_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap071System
    let c := nativeIndividualRow 71 (k+1) (nativeOld 71)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 71 = nativeGap071Old := by
    unfold nativeOld
    rw [nativeGap071Raw_formula]
    exact nativeGap071Old_formula
  rw [ho]
  have hz : nativeGap071Scale ≠ 0 := by norm_num [nativeGap071Scale]
  have hs := native_individual_scaled_source_row 71 k nativeGap071Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap071Scale hz hk
  dsimp only at hs
  rw [nativeGap071Coefficients_formula, nativeGap071System_formula] at hs
  exact hs

theorem native_gap072_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap072System
    let c := nativeIndividualRow 72 (k+1) (nativeOld 72)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 72 = nativeGap072Old := by
    unfold nativeOld
    rw [nativeGap072Raw_formula]
    exact nativeGap072Old_formula
  rw [ho]
  have hz : nativeGap072Scale ≠ 0 := by norm_num [nativeGap072Scale]
  have hs := native_individual_scaled_source_row 72 k nativeGap072Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap072Scale hz hk
  dsimp only at hs
  rw [nativeGap072Coefficients_formula, nativeGap072System_formula] at hs
  exact hs

theorem native_gap073_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap073System
    let c := nativeIndividualRow 73 (k+1) (nativeOld 73)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 73 = nativeGap073Old := by
    unfold nativeOld
    rw [nativeGap073Raw_formula]
    exact nativeGap073Old_formula
  rw [ho]
  have hz : nativeGap073Scale ≠ 0 := by norm_num [nativeGap073Scale]
  have hs := native_individual_scaled_source_row 73 k nativeGap073Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap073Scale hz hk
  dsimp only at hs
  rw [nativeGap073Coefficients_formula, nativeGap073System_formula] at hs
  exact hs

theorem native_gap074_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap074System
    let c := nativeIndividualRow 74 (k+1) (nativeOld 74)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 74 = nativeGap074Old := by
    unfold nativeOld
    rw [nativeGap074Raw_formula]
    exact nativeGap074Old_formula
  rw [ho]
  have hz : nativeGap074Scale ≠ 0 := by norm_num [nativeGap074Scale]
  have hs := native_individual_scaled_source_row 74 k nativeGap074Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap074Scale hz hk
  dsimp only at hs
  rw [nativeGap074Coefficients_formula, nativeGap074System_formula] at hs
  exact hs

theorem native_gap075_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap075System
    let c := nativeIndividualRow 75 (k+1) (nativeOld 75)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 75 = nativeGap075Old := by
    unfold nativeOld
    rw [nativeGap075Raw_formula]
    exact nativeGap075Old_formula
  rw [ho]
  have hz : nativeGap075Scale ≠ 0 := by norm_num [nativeGap075Scale]
  have hs := native_individual_scaled_source_row 75 k nativeGap075Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap075Scale hz hk
  dsimp only at hs
  rw [nativeGap075Coefficients_formula, nativeGap075System_formula] at hs
  exact hs

theorem native_gap076_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap076System
    let c := nativeIndividualRow 76 (k+1) (nativeOld 76)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 76 = nativeGap076Old := by
    unfold nativeOld
    rw [nativeGap076Raw_formula]
    exact nativeGap076Old_formula
  rw [ho]
  have hz : nativeGap076Scale ≠ 0 := by norm_num [nativeGap076Scale]
  have hs := native_individual_scaled_source_row 76 k nativeGap076Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap076Scale hz hk
  dsimp only at hs
  rw [nativeGap076Coefficients_formula, nativeGap076System_formula] at hs
  exact hs

theorem native_gap077_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap077System
    let c := nativeIndividualRow 77 (k+1) (nativeOld 77)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 77 = nativeGap077Old := by
    unfold nativeOld
    rw [nativeGap077Raw_formula]
    exact nativeGap077Old_formula
  rw [ho]
  have hz : nativeGap077Scale ≠ 0 := by norm_num [nativeGap077Scale]
  have hs := native_individual_scaled_source_row 77 k nativeGap077Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap077Scale hz hk
  dsimp only at hs
  rw [nativeGap077Coefficients_formula, nativeGap077System_formula] at hs
  exact hs

theorem native_gap078_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap078System
    let c := nativeIndividualRow 78 (k+1) (nativeOld 78)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 78 = nativeGap078Old := by
    unfold nativeOld
    rw [nativeGap078Raw_formula]
    exact nativeGap078Old_formula
  rw [ho]
  have hz : nativeGap078Scale ≠ 0 := by norm_num [nativeGap078Scale]
  have hs := native_individual_scaled_source_row 78 k nativeGap078Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap078Scale hz hk
  dsimp only at hs
  rw [nativeGap078Coefficients_formula, nativeGap078System_formula] at hs
  exact hs

theorem native_gap079_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap079System
    let c := nativeIndividualRow 79 (k+1) (nativeOld 79)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 79 = nativeGap079Old := by
    unfold nativeOld
    rw [nativeGap079Raw_formula]
    exact nativeGap079Old_formula
  rw [ho]
  have hz : nativeGap079Scale ≠ 0 := by norm_num [nativeGap079Scale]
  have hs := native_individual_scaled_source_row 79 k nativeGap079Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap079Scale hz hk
  dsimp only at hs
  rw [nativeGap079Coefficients_formula, nativeGap079System_formula] at hs
  exact hs

theorem native_gap080_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap080System
    let c := nativeIndividualRow 80 (k+1) (nativeOld 80)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 80 = nativeGap080Old := by
    unfold nativeOld
    rw [nativeGap080Raw_formula]
    exact nativeGap080Old_formula
  rw [ho]
  have hz : nativeGap080Scale ≠ 0 := by norm_num [nativeGap080Scale]
  have hs := native_individual_scaled_source_row 80 k nativeGap080Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap080Scale hz hk
  dsimp only at hs
  rw [nativeGap080Coefficients_formula, nativeGap080System_formula] at hs
  exact hs

theorem native_gap081_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap081System
    let c := nativeIndividualRow 81 (k+1) (nativeOld 81)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 81 = nativeGap081Old := by
    unfold nativeOld
    rw [nativeGap081Raw_formula]
    exact nativeGap081Old_formula
  rw [ho]
  have hz : nativeGap081Scale ≠ 0 := by norm_num [nativeGap081Scale]
  have hs := native_individual_scaled_source_row 81 k nativeGap081Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap081Scale hz hk
  dsimp only at hs
  rw [nativeGap081Coefficients_formula, nativeGap081System_formula] at hs
  exact hs

theorem native_gap082_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap082System
    let c := nativeIndividualRow 82 (k+1) (nativeOld 82)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 82 = nativeGap082Old := by
    unfold nativeOld
    rw [nativeGap082Raw_formula]
    exact nativeGap082Old_formula
  rw [ho]
  have hz : nativeGap082Scale ≠ 0 := by norm_num [nativeGap082Scale]
  have hs := native_individual_scaled_source_row 82 k nativeGap082Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap082Scale hz hk
  dsimp only at hs
  rw [nativeGap082Coefficients_formula, nativeGap082System_formula] at hs
  exact hs

theorem native_gap083_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap083System
    let c := nativeIndividualRow 83 (k+1) (nativeOld 83)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 83 = nativeGap083Old := by
    unfold nativeOld
    rw [nativeGap083Raw_formula]
    exact nativeGap083Old_formula
  rw [ho]
  have hz : nativeGap083Scale ≠ 0 := by norm_num [nativeGap083Scale]
  have hs := native_individual_scaled_source_row 83 k nativeGap083Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap083Scale hz hk
  dsimp only at hs
  rw [nativeGap083Coefficients_formula, nativeGap083System_formula] at hs
  exact hs

theorem native_gap084_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap084System
    let c := nativeIndividualRow 84 (k+1) (nativeOld 84)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 84 = nativeGap084Old := by
    unfold nativeOld
    rw [nativeGap084Raw_formula]
    exact nativeGap084Old_formula
  rw [ho]
  have hz : nativeGap084Scale ≠ 0 := by norm_num [nativeGap084Scale]
  have hs := native_individual_scaled_source_row 84 k nativeGap084Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap084Scale hz hk
  dsimp only at hs
  rw [nativeGap084Coefficients_formula, nativeGap084System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
