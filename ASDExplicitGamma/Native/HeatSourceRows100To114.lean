module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap100Inputs
public import ASDExplicitGamma.Numerics.Native.Gap101Inputs
public import ASDExplicitGamma.Numerics.Native.Gap102Inputs
public import ASDExplicitGamma.Numerics.Native.Gap103Inputs
public import ASDExplicitGamma.Numerics.Native.Gap104Inputs
public import ASDExplicitGamma.Numerics.Native.Gap105Inputs
public import ASDExplicitGamma.Numerics.Native.Gap106Inputs
public import ASDExplicitGamma.Numerics.Native.Gap107Inputs
public import ASDExplicitGamma.Numerics.Native.Gap108Inputs
public import ASDExplicitGamma.Numerics.Native.Gap109Inputs
public import ASDExplicitGamma.Numerics.Native.Gap110Inputs
public import ASDExplicitGamma.Numerics.Native.Gap111Inputs
public import ASDExplicitGamma.Numerics.Native.Gap112Inputs
public import ASDExplicitGamma.Numerics.Native.Gap113Inputs
public import ASDExplicitGamma.Numerics.Native.Gap114Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap100_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap100System
    let c := nativeIndividualRow 100 (k+1) (nativeOld 100)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 100 = nativeGap100Old := by
    unfold nativeOld
    rw [nativeGap100Raw_formula]
    exact nativeGap100Old_formula
  rw [ho]
  have hz : nativeGap100Scale ≠ 0 := by norm_num [nativeGap100Scale]
  have hs := native_individual_scaled_source_row 100 k nativeGap100Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap100Scale hz hk
  dsimp only at hs
  rw [nativeGap100Coefficients_formula, nativeGap100System_formula] at hs
  exact hs

theorem native_gap101_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap101System
    let c := nativeIndividualRow 101 (k+1) (nativeOld 101)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 101 = nativeGap101Old := by
    unfold nativeOld
    rw [nativeGap101Raw_formula]
    exact nativeGap101Old_formula
  rw [ho]
  have hz : nativeGap101Scale ≠ 0 := by norm_num [nativeGap101Scale]
  have hs := native_individual_scaled_source_row 101 k nativeGap101Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap101Scale hz hk
  dsimp only at hs
  rw [nativeGap101Coefficients_formula, nativeGap101System_formula] at hs
  exact hs

theorem native_gap102_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap102System
    let c := nativeIndividualRow 102 (k+1) (nativeOld 102)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 102 = nativeGap102Old := by
    unfold nativeOld
    rw [nativeGap102Raw_formula]
    exact nativeGap102Old_formula
  rw [ho]
  have hz : nativeGap102Scale ≠ 0 := by norm_num [nativeGap102Scale]
  have hs := native_individual_scaled_source_row 102 k nativeGap102Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap102Scale hz hk
  dsimp only at hs
  rw [nativeGap102Coefficients_formula, nativeGap102System_formula] at hs
  exact hs

theorem native_gap103_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap103System
    let c := nativeIndividualRow 103 (k+1) (nativeOld 103)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 103 = nativeGap103Old := by
    unfold nativeOld
    rw [nativeGap103Raw_formula]
    exact nativeGap103Old_formula
  rw [ho]
  have hz : nativeGap103Scale ≠ 0 := by norm_num [nativeGap103Scale]
  have hs := native_individual_scaled_source_row 103 k nativeGap103Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap103Scale hz hk
  dsimp only at hs
  rw [nativeGap103Coefficients_formula, nativeGap103System_formula] at hs
  exact hs

theorem native_gap104_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap104System
    let c := nativeIndividualRow 104 (k+1) (nativeOld 104)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 104 = nativeGap104Old := by
    unfold nativeOld
    rw [nativeGap104Raw_formula]
    exact nativeGap104Old_formula
  rw [ho]
  have hz : nativeGap104Scale ≠ 0 := by norm_num [nativeGap104Scale]
  have hs := native_individual_scaled_source_row 104 k nativeGap104Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap104Scale hz hk
  dsimp only at hs
  rw [nativeGap104Coefficients_formula, nativeGap104System_formula] at hs
  exact hs

theorem native_gap105_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap105System
    let c := nativeIndividualRow 105 (k+1) (nativeOld 105)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 105 = nativeGap105Old := by
    unfold nativeOld
    rw [nativeGap105Raw_formula]
    exact nativeGap105Old_formula
  rw [ho]
  have hz : nativeGap105Scale ≠ 0 := by norm_num [nativeGap105Scale]
  have hs := native_individual_scaled_source_row 105 k nativeGap105Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap105Scale hz hk
  dsimp only at hs
  rw [nativeGap105Coefficients_formula, nativeGap105System_formula] at hs
  exact hs

theorem native_gap106_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap106System
    let c := nativeIndividualRow 106 (k+1) (nativeOld 106)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 106 = nativeGap106Old := by
    unfold nativeOld
    rw [nativeGap106Raw_formula]
    exact nativeGap106Old_formula
  rw [ho]
  have hz : nativeGap106Scale ≠ 0 := by norm_num [nativeGap106Scale]
  have hs := native_individual_scaled_source_row 106 k nativeGap106Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap106Scale hz hk
  dsimp only at hs
  rw [nativeGap106Coefficients_formula, nativeGap106System_formula] at hs
  exact hs

theorem native_gap107_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap107System
    let c := nativeIndividualRow 107 (k+1) (nativeOld 107)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 107 = nativeGap107Old := by
    unfold nativeOld
    rw [nativeGap107Raw_formula]
    exact nativeGap107Old_formula
  rw [ho]
  have hz : nativeGap107Scale ≠ 0 := by norm_num [nativeGap107Scale]
  have hs := native_individual_scaled_source_row 107 k nativeGap107Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap107Scale hz hk
  dsimp only at hs
  rw [nativeGap107Coefficients_formula, nativeGap107System_formula] at hs
  exact hs

theorem native_gap108_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap108System
    let c := nativeIndividualRow 108 (k+1) (nativeOld 108)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 108 = nativeGap108Old := by
    unfold nativeOld
    rw [nativeGap108Raw_formula]
    exact nativeGap108Old_formula
  rw [ho]
  have hz : nativeGap108Scale ≠ 0 := by norm_num [nativeGap108Scale]
  have hs := native_individual_scaled_source_row 108 k nativeGap108Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap108Scale hz hk
  dsimp only at hs
  rw [nativeGap108Coefficients_formula, nativeGap108System_formula] at hs
  exact hs

theorem native_gap109_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap109System
    let c := nativeIndividualRow 109 (k+1) (nativeOld 109)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 109 = nativeGap109Old := by
    unfold nativeOld
    rw [nativeGap109Raw_formula]
    exact nativeGap109Old_formula
  rw [ho]
  have hz : nativeGap109Scale ≠ 0 := by norm_num [nativeGap109Scale]
  have hs := native_individual_scaled_source_row 109 k nativeGap109Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap109Scale hz hk
  dsimp only at hs
  rw [nativeGap109Coefficients_formula, nativeGap109System_formula] at hs
  exact hs

theorem native_gap110_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap110System
    let c := nativeIndividualRow 110 (k+1) (nativeOld 110)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 110 = nativeGap110Old := by
    unfold nativeOld
    rw [nativeGap110Raw_formula]
    exact nativeGap110Old_formula
  rw [ho]
  have hz : nativeGap110Scale ≠ 0 := by norm_num [nativeGap110Scale]
  have hs := native_individual_scaled_source_row 110 k nativeGap110Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap110Scale hz hk
  dsimp only at hs
  rw [nativeGap110Coefficients_formula, nativeGap110System_formula] at hs
  exact hs

theorem native_gap111_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap111System
    let c := nativeIndividualRow 111 (k+1) (nativeOld 111)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 111 = nativeGap111Old := by
    unfold nativeOld
    rw [nativeGap111Raw_formula]
    exact nativeGap111Old_formula
  rw [ho]
  have hz : nativeGap111Scale ≠ 0 := by norm_num [nativeGap111Scale]
  have hs := native_individual_scaled_source_row 111 k nativeGap111Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap111Scale hz hk
  dsimp only at hs
  rw [nativeGap111Coefficients_formula, nativeGap111System_formula] at hs
  exact hs

theorem native_gap112_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap112System
    let c := nativeIndividualRow 112 (k+1) (nativeOld 112)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 112 = nativeGap112Old := by
    unfold nativeOld
    rw [nativeGap112Raw_formula]
    exact nativeGap112Old_formula
  rw [ho]
  have hz : nativeGap112Scale ≠ 0 := by norm_num [nativeGap112Scale]
  have hs := native_individual_scaled_source_row 112 k nativeGap112Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap112Scale hz hk
  dsimp only at hs
  rw [nativeGap112Coefficients_formula, nativeGap112System_formula] at hs
  exact hs

theorem native_gap113_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap113System
    let c := nativeIndividualRow 113 (k+1) (nativeOld 113)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 113 = nativeGap113Old := by
    unfold nativeOld
    rw [nativeGap113Raw_formula]
    exact nativeGap113Old_formula
  rw [ho]
  have hz : nativeGap113Scale ≠ 0 := by norm_num [nativeGap113Scale]
  have hs := native_individual_scaled_source_row 113 k nativeGap113Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap113Scale hz hk
  dsimp only at hs
  rw [nativeGap113Coefficients_formula, nativeGap113System_formula] at hs
  exact hs

theorem native_gap114_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap114System
    let c := nativeIndividualRow 114 (k+1) (nativeOld 114)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 114 = nativeGap114Old := by
    unfold nativeOld
    rw [nativeGap114Raw_formula]
    exact nativeGap114Old_formula
  rw [ho]
  have hz : nativeGap114Scale ≠ 0 := by norm_num [nativeGap114Scale]
  have hs := native_individual_scaled_source_row 114 k nativeGap114Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap114Scale hz hk
  dsimp only at hs
  rw [nativeGap114Coefficients_formula, nativeGap114System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
