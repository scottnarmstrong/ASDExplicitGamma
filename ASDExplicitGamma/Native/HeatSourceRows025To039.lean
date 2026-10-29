module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap025Inputs
public import ASDExplicitGamma.Numerics.Native.Gap026Inputs
public import ASDExplicitGamma.Numerics.Native.Gap027Inputs
public import ASDExplicitGamma.Numerics.Native.Gap028Inputs
public import ASDExplicitGamma.Numerics.Native.Gap029Inputs
public import ASDExplicitGamma.Numerics.Native.Gap030Inputs
public import ASDExplicitGamma.Numerics.Native.Gap031Inputs
public import ASDExplicitGamma.Numerics.Native.Gap032Inputs
public import ASDExplicitGamma.Numerics.Native.Gap033Inputs
public import ASDExplicitGamma.Numerics.Native.Gap034Inputs
public import ASDExplicitGamma.Numerics.Native.Gap035Inputs
public import ASDExplicitGamma.Numerics.Native.Gap036Inputs
public import ASDExplicitGamma.Numerics.Native.Gap037Inputs
public import ASDExplicitGamma.Numerics.Native.Gap038Inputs
public import ASDExplicitGamma.Numerics.Native.Gap039Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap025_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap025System
    let c := nativeIndividualRow 25 (k+1) (nativeOld 25)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 25 = nativeGap025Old := by
    unfold nativeOld
    rw [nativeGap025Raw_formula]
    exact nativeGap025Old_formula
  rw [ho]
  have hz : nativeGap025Scale ≠ 0 := by norm_num [nativeGap025Scale]
  have hs := native_individual_scaled_source_row 25 k nativeGap025Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap025Scale hz hk
  dsimp only at hs
  rw [nativeGap025Coefficients_formula, nativeGap025System_formula] at hs
  exact hs

theorem native_gap026_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap026System
    let c := nativeIndividualRow 26 (k+1) (nativeOld 26)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 26 = nativeGap026Old := by
    unfold nativeOld
    rw [nativeGap026Raw_formula]
    exact nativeGap026Old_formula
  rw [ho]
  have hz : nativeGap026Scale ≠ 0 := by norm_num [nativeGap026Scale]
  have hs := native_individual_scaled_source_row 26 k nativeGap026Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap026Scale hz hk
  dsimp only at hs
  rw [nativeGap026Coefficients_formula, nativeGap026System_formula] at hs
  exact hs

theorem native_gap027_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap027System
    let c := nativeIndividualRow 27 (k+1) (nativeOld 27)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 27 = nativeGap027Old := by
    unfold nativeOld
    rw [nativeGap027Raw_formula]
    exact nativeGap027Old_formula
  rw [ho]
  have hz : nativeGap027Scale ≠ 0 := by norm_num [nativeGap027Scale]
  have hs := native_individual_scaled_source_row 27 k nativeGap027Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap027Scale hz hk
  dsimp only at hs
  rw [nativeGap027Coefficients_formula, nativeGap027System_formula] at hs
  exact hs

theorem native_gap028_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap028System
    let c := nativeIndividualRow 28 (k+1) (nativeOld 28)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 28 = nativeGap028Old := by
    unfold nativeOld
    rw [nativeGap028Raw_formula]
    exact nativeGap028Old_formula
  rw [ho]
  have hz : nativeGap028Scale ≠ 0 := by norm_num [nativeGap028Scale]
  have hs := native_individual_scaled_source_row 28 k nativeGap028Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap028Scale hz hk
  dsimp only at hs
  rw [nativeGap028Coefficients_formula, nativeGap028System_formula] at hs
  exact hs

theorem native_gap029_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap029System
    let c := nativeIndividualRow 29 (k+1) (nativeOld 29)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 29 = nativeGap029Old := by
    unfold nativeOld
    rw [nativeGap029Raw_formula]
    exact nativeGap029Old_formula
  rw [ho]
  have hz : nativeGap029Scale ≠ 0 := by norm_num [nativeGap029Scale]
  have hs := native_individual_scaled_source_row 29 k nativeGap029Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap029Scale hz hk
  dsimp only at hs
  rw [nativeGap029Coefficients_formula, nativeGap029System_formula] at hs
  exact hs

theorem native_gap030_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap030System
    let c := nativeIndividualRow 30 (k+1) (nativeOld 30)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 30 = nativeGap030Old := by
    unfold nativeOld
    rw [nativeGap030Raw_formula]
    exact nativeGap030Old_formula
  rw [ho]
  have hz : nativeGap030Scale ≠ 0 := by norm_num [nativeGap030Scale]
  have hs := native_individual_scaled_source_row 30 k nativeGap030Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap030Scale hz hk
  dsimp only at hs
  rw [nativeGap030Coefficients_formula, nativeGap030System_formula] at hs
  exact hs

theorem native_gap031_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap031System
    let c := nativeIndividualRow 31 (k+1) (nativeOld 31)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 31 = nativeGap031Old := by
    unfold nativeOld
    rw [nativeGap031Raw_formula]
    exact nativeGap031Old_formula
  rw [ho]
  have hz : nativeGap031Scale ≠ 0 := by norm_num [nativeGap031Scale]
  have hs := native_individual_scaled_source_row 31 k nativeGap031Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap031Scale hz hk
  dsimp only at hs
  rw [nativeGap031Coefficients_formula, nativeGap031System_formula] at hs
  exact hs

theorem native_gap032_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap032System
    let c := nativeIndividualRow 32 (k+1) (nativeOld 32)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 32 = nativeGap032Old := by
    unfold nativeOld
    rw [nativeGap032Raw_formula]
    exact nativeGap032Old_formula
  rw [ho]
  have hz : nativeGap032Scale ≠ 0 := by norm_num [nativeGap032Scale]
  have hs := native_individual_scaled_source_row 32 k nativeGap032Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap032Scale hz hk
  dsimp only at hs
  rw [nativeGap032Coefficients_formula, nativeGap032System_formula] at hs
  exact hs

theorem native_gap033_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap033System
    let c := nativeIndividualRow 33 (k+1) (nativeOld 33)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 33 = nativeGap033Old := by
    unfold nativeOld
    rw [nativeGap033Raw_formula]
    exact nativeGap033Old_formula
  rw [ho]
  have hz : nativeGap033Scale ≠ 0 := by norm_num [nativeGap033Scale]
  have hs := native_individual_scaled_source_row 33 k nativeGap033Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap033Scale hz hk
  dsimp only at hs
  rw [nativeGap033Coefficients_formula, nativeGap033System_formula] at hs
  exact hs

theorem native_gap034_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap034System
    let c := nativeIndividualRow 34 (k+1) (nativeOld 34)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 34 = nativeGap034Old := by
    unfold nativeOld
    rw [nativeGap034Raw_formula]
    exact nativeGap034Old_formula
  rw [ho]
  have hz : nativeGap034Scale ≠ 0 := by norm_num [nativeGap034Scale]
  have hs := native_individual_scaled_source_row 34 k nativeGap034Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap034Scale hz hk
  dsimp only at hs
  rw [nativeGap034Coefficients_formula, nativeGap034System_formula] at hs
  exact hs

theorem native_gap035_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap035System
    let c := nativeIndividualRow 35 (k+1) (nativeOld 35)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 35 = nativeGap035Old := by
    unfold nativeOld
    rw [nativeGap035Raw_formula]
    exact nativeGap035Old_formula
  rw [ho]
  have hz : nativeGap035Scale ≠ 0 := by norm_num [nativeGap035Scale]
  have hs := native_individual_scaled_source_row 35 k nativeGap035Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap035Scale hz hk
  dsimp only at hs
  rw [nativeGap035Coefficients_formula, nativeGap035System_formula] at hs
  exact hs

theorem native_gap036_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap036System
    let c := nativeIndividualRow 36 (k+1) (nativeOld 36)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 36 = nativeGap036Old := by
    unfold nativeOld
    rw [nativeGap036Raw_formula]
    exact nativeGap036Old_formula
  rw [ho]
  have hz : nativeGap036Scale ≠ 0 := by norm_num [nativeGap036Scale]
  have hs := native_individual_scaled_source_row 36 k nativeGap036Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap036Scale hz hk
  dsimp only at hs
  rw [nativeGap036Coefficients_formula, nativeGap036System_formula] at hs
  exact hs

theorem native_gap037_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap037System
    let c := nativeIndividualRow 37 (k+1) (nativeOld 37)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 37 = nativeGap037Old := by
    unfold nativeOld
    rw [nativeGap037Raw_formula]
    exact nativeGap037Old_formula
  rw [ho]
  have hz : nativeGap037Scale ≠ 0 := by norm_num [nativeGap037Scale]
  have hs := native_individual_scaled_source_row 37 k nativeGap037Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap037Scale hz hk
  dsimp only at hs
  rw [nativeGap037Coefficients_formula, nativeGap037System_formula] at hs
  exact hs

theorem native_gap038_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap038System
    let c := nativeIndividualRow 38 (k+1) (nativeOld 38)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 38 = nativeGap038Old := by
    unfold nativeOld
    rw [nativeGap038Raw_formula]
    exact nativeGap038Old_formula
  rw [ho]
  have hz : nativeGap038Scale ≠ 0 := by norm_num [nativeGap038Scale]
  have hs := native_individual_scaled_source_row 38 k nativeGap038Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap038Scale hz hk
  dsimp only at hs
  rw [nativeGap038Coefficients_formula, nativeGap038System_formula] at hs
  exact hs

theorem native_gap039_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap039System
    let c := nativeIndividualRow 39 (k+1) (nativeOld 39)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 39 = nativeGap039Old := by
    unfold nativeOld
    rw [nativeGap039Raw_formula]
    exact nativeGap039Old_formula
  rw [ho]
  have hz : nativeGap039Scale ≠ 0 := by norm_num [nativeGap039Scale]
  have hs := native_individual_scaled_source_row 39 k nativeGap039Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap039Scale hz hk
  dsimp only at hs
  rw [nativeGap039Coefficients_formula, nativeGap039System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
