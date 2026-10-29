module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap055Inputs
public import ASDExplicitGamma.Numerics.Native.Gap056Inputs
public import ASDExplicitGamma.Numerics.Native.Gap057Inputs
public import ASDExplicitGamma.Numerics.Native.Gap058Inputs
public import ASDExplicitGamma.Numerics.Native.Gap059Inputs
public import ASDExplicitGamma.Numerics.Native.Gap060Inputs
public import ASDExplicitGamma.Numerics.Native.Gap061Inputs
public import ASDExplicitGamma.Numerics.Native.Gap062Inputs
public import ASDExplicitGamma.Numerics.Native.Gap063Inputs
public import ASDExplicitGamma.Numerics.Native.Gap064Inputs
public import ASDExplicitGamma.Numerics.Native.Gap065Inputs
public import ASDExplicitGamma.Numerics.Native.Gap066Inputs
public import ASDExplicitGamma.Numerics.Native.Gap067Inputs
public import ASDExplicitGamma.Numerics.Native.Gap068Inputs
public import ASDExplicitGamma.Numerics.Native.Gap069Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap055_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap055System
    let c := nativeIndividualRow 55 (k+1) (nativeOld 55)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 55 = nativeGap055Old := by
    unfold nativeOld
    rw [nativeGap055Raw_formula]
    exact nativeGap055Old_formula
  rw [ho]
  have hz : nativeGap055Scale ≠ 0 := by norm_num [nativeGap055Scale]
  have hs := native_individual_scaled_source_row 55 k nativeGap055Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap055Scale hz hk
  dsimp only at hs
  rw [nativeGap055Coefficients_formula, nativeGap055System_formula] at hs
  exact hs

theorem native_gap056_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap056System
    let c := nativeIndividualRow 56 (k+1) (nativeOld 56)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 56 = nativeGap056Old := by
    unfold nativeOld
    rw [nativeGap056Raw_formula]
    exact nativeGap056Old_formula
  rw [ho]
  have hz : nativeGap056Scale ≠ 0 := by norm_num [nativeGap056Scale]
  have hs := native_individual_scaled_source_row 56 k nativeGap056Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap056Scale hz hk
  dsimp only at hs
  rw [nativeGap056Coefficients_formula, nativeGap056System_formula] at hs
  exact hs

theorem native_gap057_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap057System
    let c := nativeIndividualRow 57 (k+1) (nativeOld 57)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 57 = nativeGap057Old := by
    unfold nativeOld
    rw [nativeGap057Raw_formula]
    exact nativeGap057Old_formula
  rw [ho]
  have hz : nativeGap057Scale ≠ 0 := by norm_num [nativeGap057Scale]
  have hs := native_individual_scaled_source_row 57 k nativeGap057Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap057Scale hz hk
  dsimp only at hs
  rw [nativeGap057Coefficients_formula, nativeGap057System_formula] at hs
  exact hs

theorem native_gap058_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap058System
    let c := nativeIndividualRow 58 (k+1) (nativeOld 58)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 58 = nativeGap058Old := by
    unfold nativeOld
    rw [nativeGap058Raw_formula]
    exact nativeGap058Old_formula
  rw [ho]
  have hz : nativeGap058Scale ≠ 0 := by norm_num [nativeGap058Scale]
  have hs := native_individual_scaled_source_row 58 k nativeGap058Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap058Scale hz hk
  dsimp only at hs
  rw [nativeGap058Coefficients_formula, nativeGap058System_formula] at hs
  exact hs

theorem native_gap059_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap059System
    let c := nativeIndividualRow 59 (k+1) (nativeOld 59)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 59 = nativeGap059Old := by
    unfold nativeOld
    rw [nativeGap059Raw_formula]
    exact nativeGap059Old_formula
  rw [ho]
  have hz : nativeGap059Scale ≠ 0 := by norm_num [nativeGap059Scale]
  have hs := native_individual_scaled_source_row 59 k nativeGap059Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap059Scale hz hk
  dsimp only at hs
  rw [nativeGap059Coefficients_formula, nativeGap059System_formula] at hs
  exact hs

theorem native_gap060_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap060System
    let c := nativeIndividualRow 60 (k+1) (nativeOld 60)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 60 = nativeGap060Old := by
    unfold nativeOld
    rw [nativeGap060Raw_formula]
    exact nativeGap060Old_formula
  rw [ho]
  have hz : nativeGap060Scale ≠ 0 := by norm_num [nativeGap060Scale]
  have hs := native_individual_scaled_source_row 60 k nativeGap060Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap060Scale hz hk
  dsimp only at hs
  rw [nativeGap060Coefficients_formula, nativeGap060System_formula] at hs
  exact hs

theorem native_gap061_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap061System
    let c := nativeIndividualRow 61 (k+1) (nativeOld 61)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 61 = nativeGap061Old := by
    unfold nativeOld
    rw [nativeGap061Raw_formula]
    exact nativeGap061Old_formula
  rw [ho]
  have hz : nativeGap061Scale ≠ 0 := by norm_num [nativeGap061Scale]
  have hs := native_individual_scaled_source_row 61 k nativeGap061Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap061Scale hz hk
  dsimp only at hs
  rw [nativeGap061Coefficients_formula, nativeGap061System_formula] at hs
  exact hs

theorem native_gap062_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap062System
    let c := nativeIndividualRow 62 (k+1) (nativeOld 62)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 62 = nativeGap062Old := by
    unfold nativeOld
    rw [nativeGap062Raw_formula]
    exact nativeGap062Old_formula
  rw [ho]
  have hz : nativeGap062Scale ≠ 0 := by norm_num [nativeGap062Scale]
  have hs := native_individual_scaled_source_row 62 k nativeGap062Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap062Scale hz hk
  dsimp only at hs
  rw [nativeGap062Coefficients_formula, nativeGap062System_formula] at hs
  exact hs

theorem native_gap063_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap063System
    let c := nativeIndividualRow 63 (k+1) (nativeOld 63)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 63 = nativeGap063Old := by
    unfold nativeOld
    rw [nativeGap063Raw_formula]
    exact nativeGap063Old_formula
  rw [ho]
  have hz : nativeGap063Scale ≠ 0 := by norm_num [nativeGap063Scale]
  have hs := native_individual_scaled_source_row 63 k nativeGap063Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap063Scale hz hk
  dsimp only at hs
  rw [nativeGap063Coefficients_formula, nativeGap063System_formula] at hs
  exact hs

theorem native_gap064_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap064System
    let c := nativeIndividualRow 64 (k+1) (nativeOld 64)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 64 = nativeGap064Old := by
    unfold nativeOld
    rw [nativeGap064Raw_formula]
    exact nativeGap064Old_formula
  rw [ho]
  have hz : nativeGap064Scale ≠ 0 := by norm_num [nativeGap064Scale]
  have hs := native_individual_scaled_source_row 64 k nativeGap064Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap064Scale hz hk
  dsimp only at hs
  rw [nativeGap064Coefficients_formula, nativeGap064System_formula] at hs
  exact hs

theorem native_gap065_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap065System
    let c := nativeIndividualRow 65 (k+1) (nativeOld 65)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 65 = nativeGap065Old := by
    unfold nativeOld
    rw [nativeGap065Raw_formula]
    exact nativeGap065Old_formula
  rw [ho]
  have hz : nativeGap065Scale ≠ 0 := by norm_num [nativeGap065Scale]
  have hs := native_individual_scaled_source_row 65 k nativeGap065Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap065Scale hz hk
  dsimp only at hs
  rw [nativeGap065Coefficients_formula, nativeGap065System_formula] at hs
  exact hs

theorem native_gap066_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap066System
    let c := nativeIndividualRow 66 (k+1) (nativeOld 66)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 66 = nativeGap066Old := by
    unfold nativeOld
    rw [nativeGap066Raw_formula]
    exact nativeGap066Old_formula
  rw [ho]
  have hz : nativeGap066Scale ≠ 0 := by norm_num [nativeGap066Scale]
  have hs := native_individual_scaled_source_row 66 k nativeGap066Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap066Scale hz hk
  dsimp only at hs
  rw [nativeGap066Coefficients_formula, nativeGap066System_formula] at hs
  exact hs

theorem native_gap067_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap067System
    let c := nativeIndividualRow 67 (k+1) (nativeOld 67)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 67 = nativeGap067Old := by
    unfold nativeOld
    rw [nativeGap067Raw_formula]
    exact nativeGap067Old_formula
  rw [ho]
  have hz : nativeGap067Scale ≠ 0 := by norm_num [nativeGap067Scale]
  have hs := native_individual_scaled_source_row 67 k nativeGap067Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap067Scale hz hk
  dsimp only at hs
  rw [nativeGap067Coefficients_formula, nativeGap067System_formula] at hs
  exact hs

theorem native_gap068_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap068System
    let c := nativeIndividualRow 68 (k+1) (nativeOld 68)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 68 = nativeGap068Old := by
    unfold nativeOld
    rw [nativeGap068Raw_formula]
    exact nativeGap068Old_formula
  rw [ho]
  have hz : nativeGap068Scale ≠ 0 := by norm_num [nativeGap068Scale]
  have hs := native_individual_scaled_source_row 68 k nativeGap068Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap068Scale hz hk
  dsimp only at hs
  rw [nativeGap068Coefficients_formula, nativeGap068System_formula] at hs
  exact hs

theorem native_gap069_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap069System
    let c := nativeIndividualRow 69 (k+1) (nativeOld 69)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 69 = nativeGap069Old := by
    unfold nativeOld
    rw [nativeGap069Raw_formula]
    exact nativeGap069Old_formula
  rw [ho]
  have hz : nativeGap069Scale ≠ 0 := by norm_num [nativeGap069Scale]
  have hs := native_individual_scaled_source_row 69 k nativeGap069Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap069Scale hz hk
  dsimp only at hs
  rw [nativeGap069Coefficients_formula, nativeGap069System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
