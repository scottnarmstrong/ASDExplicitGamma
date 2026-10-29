module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap001Inputs
public import ASDExplicitGamma.Numerics.Native.Gap011Inputs
public import ASDExplicitGamma.Numerics.Native.Gap012Inputs
public import ASDExplicitGamma.Numerics.Native.Gap013Inputs
public import ASDExplicitGamma.Numerics.Native.Gap014Inputs
public import ASDExplicitGamma.Numerics.Native.Gap015Inputs
public import ASDExplicitGamma.Numerics.Native.Gap016Inputs
public import ASDExplicitGamma.Numerics.Native.Gap017Inputs
public import ASDExplicitGamma.Numerics.Native.Gap018Inputs
public import ASDExplicitGamma.Numerics.Native.Gap019Inputs
public import ASDExplicitGamma.Numerics.Native.Gap020Inputs
public import ASDExplicitGamma.Numerics.Native.Gap021Inputs
public import ASDExplicitGamma.Numerics.Native.Gap022Inputs
public import ASDExplicitGamma.Numerics.Native.Gap023Inputs
public import ASDExplicitGamma.Numerics.Native.Gap024Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap001_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap001System
    let c := nativeIndividualRow 1 (k+1) (nativeOld 1)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 1 = nativeGap001Old := by
    unfold nativeOld
    rw [nativeGap001Raw_formula]
    exact nativeGap001Old_formula
  rw [ho]
  have hz : nativeGap001Scale ≠ 0 := by norm_num [nativeGap001Scale]
  have hs := native_individual_scaled_source_row 1 k nativeGap001Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap001Scale hz hk
  dsimp only at hs
  rw [nativeGap001Coefficients_formula, nativeGap001System_formula] at hs
  exact hs

theorem native_gap011_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap011System
    let c := nativeIndividualRow 11 (k+1) (nativeOld 11)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 11 = nativeGap011Old := by
    unfold nativeOld
    rw [nativeGap011Raw_formula]
    exact nativeGap011Old_formula
  rw [ho]
  have hz : nativeGap011Scale ≠ 0 := by norm_num [nativeGap011Scale]
  have hs := native_individual_scaled_source_row 11 k nativeGap011Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap011Scale hz hk
  dsimp only at hs
  rw [nativeGap011Coefficients_formula, nativeGap011System_formula] at hs
  exact hs

theorem native_gap012_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap012System
    let c := nativeIndividualRow 12 (k+1) (nativeOld 12)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 12 = nativeGap012Old := by
    unfold nativeOld
    rw [nativeGap012Raw_formula]
    exact nativeGap012Old_formula
  rw [ho]
  have hz : nativeGap012Scale ≠ 0 := by norm_num [nativeGap012Scale]
  have hs := native_individual_scaled_source_row 12 k nativeGap012Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap012Scale hz hk
  dsimp only at hs
  rw [nativeGap012Coefficients_formula, nativeGap012System_formula] at hs
  exact hs

theorem native_gap013_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap013System
    let c := nativeIndividualRow 13 (k+1) (nativeOld 13)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 13 = nativeGap013Old := by
    unfold nativeOld
    rw [nativeGap013Raw_formula]
    exact nativeGap013Old_formula
  rw [ho]
  have hz : nativeGap013Scale ≠ 0 := by norm_num [nativeGap013Scale]
  have hs := native_individual_scaled_source_row 13 k nativeGap013Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap013Scale hz hk
  dsimp only at hs
  rw [nativeGap013Coefficients_formula, nativeGap013System_formula] at hs
  exact hs

theorem native_gap014_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap014System
    let c := nativeIndividualRow 14 (k+1) (nativeOld 14)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 14 = nativeGap014Old := by
    unfold nativeOld
    rw [nativeGap014Raw_formula]
    exact nativeGap014Old_formula
  rw [ho]
  have hz : nativeGap014Scale ≠ 0 := by norm_num [nativeGap014Scale]
  have hs := native_individual_scaled_source_row 14 k nativeGap014Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap014Scale hz hk
  dsimp only at hs
  rw [nativeGap014Coefficients_formula, nativeGap014System_formula] at hs
  exact hs

theorem native_gap015_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap015System
    let c := nativeIndividualRow 15 (k+1) (nativeOld 15)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 15 = nativeGap015Old := by
    unfold nativeOld
    rw [nativeGap015Raw_formula]
    exact nativeGap015Old_formula
  rw [ho]
  have hz : nativeGap015Scale ≠ 0 := by norm_num [nativeGap015Scale]
  have hs := native_individual_scaled_source_row 15 k nativeGap015Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap015Scale hz hk
  dsimp only at hs
  rw [nativeGap015Coefficients_formula, nativeGap015System_formula] at hs
  exact hs

theorem native_gap016_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap016System
    let c := nativeIndividualRow 16 (k+1) (nativeOld 16)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 16 = nativeGap016Old := by
    unfold nativeOld
    rw [nativeGap016Raw_formula]
    exact nativeGap016Old_formula
  rw [ho]
  have hz : nativeGap016Scale ≠ 0 := by norm_num [nativeGap016Scale]
  have hs := native_individual_scaled_source_row 16 k nativeGap016Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap016Scale hz hk
  dsimp only at hs
  rw [nativeGap016Coefficients_formula, nativeGap016System_formula] at hs
  exact hs

theorem native_gap017_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap017System
    let c := nativeIndividualRow 17 (k+1) (nativeOld 17)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 17 = nativeGap017Old := by
    unfold nativeOld
    rw [nativeGap017Raw_formula]
    exact nativeGap017Old_formula
  rw [ho]
  have hz : nativeGap017Scale ≠ 0 := by norm_num [nativeGap017Scale]
  have hs := native_individual_scaled_source_row 17 k nativeGap017Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap017Scale hz hk
  dsimp only at hs
  rw [nativeGap017Coefficients_formula, nativeGap017System_formula] at hs
  exact hs

theorem native_gap018_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap018System
    let c := nativeIndividualRow 18 (k+1) (nativeOld 18)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 18 = nativeGap018Old := by
    unfold nativeOld
    rw [nativeGap018Raw_formula]
    exact nativeGap018Old_formula
  rw [ho]
  have hz : nativeGap018Scale ≠ 0 := by norm_num [nativeGap018Scale]
  have hs := native_individual_scaled_source_row 18 k nativeGap018Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap018Scale hz hk
  dsimp only at hs
  rw [nativeGap018Coefficients_formula, nativeGap018System_formula] at hs
  exact hs

theorem native_gap019_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap019System
    let c := nativeIndividualRow 19 (k+1) (nativeOld 19)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 19 = nativeGap019Old := by
    unfold nativeOld
    rw [nativeGap019Raw_formula]
    exact nativeGap019Old_formula
  rw [ho]
  have hz : nativeGap019Scale ≠ 0 := by norm_num [nativeGap019Scale]
  have hs := native_individual_scaled_source_row 19 k nativeGap019Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap019Scale hz hk
  dsimp only at hs
  rw [nativeGap019Coefficients_formula, nativeGap019System_formula] at hs
  exact hs

theorem native_gap020_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap020System
    let c := nativeIndividualRow 20 (k+1) (nativeOld 20)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 20 = nativeGap020Old := by
    unfold nativeOld
    rw [nativeGap020Raw_formula]
    exact nativeGap020Old_formula
  rw [ho]
  have hz : nativeGap020Scale ≠ 0 := by norm_num [nativeGap020Scale]
  have hs := native_individual_scaled_source_row 20 k nativeGap020Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap020Scale hz hk
  dsimp only at hs
  rw [nativeGap020Coefficients_formula, nativeGap020System_formula] at hs
  exact hs

theorem native_gap021_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap021System
    let c := nativeIndividualRow 21 (k+1) (nativeOld 21)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 21 = nativeGap021Old := by
    unfold nativeOld
    rw [nativeGap021Raw_formula]
    exact nativeGap021Old_formula
  rw [ho]
  have hz : nativeGap021Scale ≠ 0 := by norm_num [nativeGap021Scale]
  have hs := native_individual_scaled_source_row 21 k nativeGap021Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap021Scale hz hk
  dsimp only at hs
  rw [nativeGap021Coefficients_formula, nativeGap021System_formula] at hs
  exact hs

theorem native_gap022_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap022System
    let c := nativeIndividualRow 22 (k+1) (nativeOld 22)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 22 = nativeGap022Old := by
    unfold nativeOld
    rw [nativeGap022Raw_formula]
    exact nativeGap022Old_formula
  rw [ho]
  have hz : nativeGap022Scale ≠ 0 := by norm_num [nativeGap022Scale]
  have hs := native_individual_scaled_source_row 22 k nativeGap022Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap022Scale hz hk
  dsimp only at hs
  rw [nativeGap022Coefficients_formula, nativeGap022System_formula] at hs
  exact hs

theorem native_gap023_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap023System
    let c := nativeIndividualRow 23 (k+1) (nativeOld 23)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 23 = nativeGap023Old := by
    unfold nativeOld
    rw [nativeGap023Raw_formula]
    exact nativeGap023Old_formula
  rw [ho]
  have hz : nativeGap023Scale ≠ 0 := by norm_num [nativeGap023Scale]
  have hs := native_individual_scaled_source_row 23 k nativeGap023Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap023Scale hz hk
  dsimp only at hs
  rw [nativeGap023Coefficients_formula, nativeGap023System_formula] at hs
  exact hs

theorem native_gap024_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap024System
    let c := nativeIndividualRow 24 (k+1) (nativeOld 24)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 24 = nativeGap024Old := by
    unfold nativeOld
    rw [nativeGap024Raw_formula]
    exact nativeGap024Old_formula
  rw [ho]
  have hz : nativeGap024Scale ≠ 0 := by norm_num [nativeGap024Scale]
  have hs := native_individual_scaled_source_row 24 k nativeGap024Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap024Scale hz hk
  dsimp only at hs
  rw [nativeGap024Coefficients_formula, nativeGap024System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
