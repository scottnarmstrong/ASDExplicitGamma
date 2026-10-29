module

public import ASDExplicitGamma.Native.HeatSourceRowScaling
public import ASDExplicitGamma.Numerics.Native.Gap085Inputs
public import ASDExplicitGamma.Numerics.Native.Gap086Inputs
public import ASDExplicitGamma.Numerics.Native.Gap087Inputs
public import ASDExplicitGamma.Numerics.Native.Gap088Inputs
public import ASDExplicitGamma.Numerics.Native.Gap089Inputs
public import ASDExplicitGamma.Numerics.Native.Gap090Inputs
public import ASDExplicitGamma.Numerics.Native.Gap091Inputs
public import ASDExplicitGamma.Numerics.Native.Gap092Inputs
public import ASDExplicitGamma.Numerics.Native.Gap093Inputs
public import ASDExplicitGamma.Numerics.Native.Gap094Inputs
public import ASDExplicitGamma.Numerics.Native.Gap095Inputs
public import ASDExplicitGamma.Numerics.Native.Gap096Inputs
public import ASDExplicitGamma.Numerics.Native.Gap097Inputs
public import ASDExplicitGamma.Numerics.Native.Gap098Inputs
public import ASDExplicitGamma.Numerics.Native.Gap099Inputs

/-! Exact individual producer rows, retaining all three coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

theorem native_gap085_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap085System
    let c := nativeIndividualRow 85 (k+1) (nativeOld 85)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 85 = nativeGap085Old := by
    unfold nativeOld
    rw [nativeGap085Raw_formula]
    exact nativeGap085Old_formula
  rw [ho]
  have hz : nativeGap085Scale ≠ 0 := by norm_num [nativeGap085Scale]
  have hs := native_individual_scaled_source_row 85 k nativeGap085Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap085Scale hz hk
  dsimp only at hs
  rw [nativeGap085Coefficients_formula, nativeGap085System_formula] at hs
  exact hs

theorem native_gap086_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap086System
    let c := nativeIndividualRow 86 (k+1) (nativeOld 86)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 86 = nativeGap086Old := by
    unfold nativeOld
    rw [nativeGap086Raw_formula]
    exact nativeGap086Old_formula
  rw [ho]
  have hz : nativeGap086Scale ≠ 0 := by norm_num [nativeGap086Scale]
  have hs := native_individual_scaled_source_row 86 k nativeGap086Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap086Scale hz hk
  dsimp only at hs
  rw [nativeGap086Coefficients_formula, nativeGap086System_formula] at hs
  exact hs

theorem native_gap087_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap087System
    let c := nativeIndividualRow 87 (k+1) (nativeOld 87)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 87 = nativeGap087Old := by
    unfold nativeOld
    rw [nativeGap087Raw_formula]
    exact nativeGap087Old_formula
  rw [ho]
  have hz : nativeGap087Scale ≠ 0 := by norm_num [nativeGap087Scale]
  have hs := native_individual_scaled_source_row 87 k nativeGap087Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap087Scale hz hk
  dsimp only at hs
  rw [nativeGap087Coefficients_formula, nativeGap087System_formula] at hs
  exact hs

theorem native_gap088_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap088System
    let c := nativeIndividualRow 88 (k+1) (nativeOld 88)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 88 = nativeGap088Old := by
    unfold nativeOld
    rw [nativeGap088Raw_formula]
    exact nativeGap088Old_formula
  rw [ho]
  have hz : nativeGap088Scale ≠ 0 := by norm_num [nativeGap088Scale]
  have hs := native_individual_scaled_source_row 88 k nativeGap088Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap088Scale hz hk
  dsimp only at hs
  rw [nativeGap088Coefficients_formula, nativeGap088System_formula] at hs
  exact hs

theorem native_gap089_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap089System
    let c := nativeIndividualRow 89 (k+1) (nativeOld 89)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 89 = nativeGap089Old := by
    unfold nativeOld
    rw [nativeGap089Raw_formula]
    exact nativeGap089Old_formula
  rw [ho]
  have hz : nativeGap089Scale ≠ 0 := by norm_num [nativeGap089Scale]
  have hs := native_individual_scaled_source_row 89 k nativeGap089Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap089Scale hz hk
  dsimp only at hs
  rw [nativeGap089Coefficients_formula, nativeGap089System_formula] at hs
  exact hs

theorem native_gap090_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap090System
    let c := nativeIndividualRow 90 (k+1) (nativeOld 90)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 90 = nativeGap090Old := by
    unfold nativeOld
    rw [nativeGap090Raw_formula]
    exact nativeGap090Old_formula
  rw [ho]
  have hz : nativeGap090Scale ≠ 0 := by norm_num [nativeGap090Scale]
  have hs := native_individual_scaled_source_row 90 k nativeGap090Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap090Scale hz hk
  dsimp only at hs
  rw [nativeGap090Coefficients_formula, nativeGap090System_formula] at hs
  exact hs

theorem native_gap091_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap091System
    let c := nativeIndividualRow 91 (k+1) (nativeOld 91)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 91 = nativeGap091Old := by
    unfold nativeOld
    rw [nativeGap091Raw_formula]
    exact nativeGap091Old_formula
  rw [ho]
  have hz : nativeGap091Scale ≠ 0 := by norm_num [nativeGap091Scale]
  have hs := native_individual_scaled_source_row 91 k nativeGap091Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap091Scale hz hk
  dsimp only at hs
  rw [nativeGap091Coefficients_formula, nativeGap091System_formula] at hs
  exact hs

theorem native_gap092_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap092System
    let c := nativeIndividualRow 92 (k+1) (nativeOld 92)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 92 = nativeGap092Old := by
    unfold nativeOld
    rw [nativeGap092Raw_formula]
    exact nativeGap092Old_formula
  rw [ho]
  have hz : nativeGap092Scale ≠ 0 := by norm_num [nativeGap092Scale]
  have hs := native_individual_scaled_source_row 92 k nativeGap092Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap092Scale hz hk
  dsimp only at hs
  rw [nativeGap092Coefficients_formula, nativeGap092System_formula] at hs
  exact hs

theorem native_gap093_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap093System
    let c := nativeIndividualRow 93 (k+1) (nativeOld 93)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 93 = nativeGap093Old := by
    unfold nativeOld
    rw [nativeGap093Raw_formula]
    exact nativeGap093Old_formula
  rw [ho]
  have hz : nativeGap093Scale ≠ 0 := by norm_num [nativeGap093Scale]
  have hs := native_individual_scaled_source_row 93 k nativeGap093Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap093Scale hz hk
  dsimp only at hs
  rw [nativeGap093Coefficients_formula, nativeGap093System_formula] at hs
  exact hs

theorem native_gap094_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap094System
    let c := nativeIndividualRow 94 (k+1) (nativeOld 94)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 94 = nativeGap094Old := by
    unfold nativeOld
    rw [nativeGap094Raw_formula]
    exact nativeGap094Old_formula
  rw [ho]
  have hz : nativeGap094Scale ≠ 0 := by norm_num [nativeGap094Scale]
  have hs := native_individual_scaled_source_row 94 k nativeGap094Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap094Scale hz hk
  dsimp only at hs
  rw [nativeGap094Coefficients_formula, nativeGap094System_formula] at hs
  exact hs

theorem native_gap095_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap095System
    let c := nativeIndividualRow 95 (k+1) (nativeOld 95)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 95 = nativeGap095Old := by
    unfold nativeOld
    rw [nativeGap095Raw_formula]
    exact nativeGap095Old_formula
  rw [ho]
  have hz : nativeGap095Scale ≠ 0 := by norm_num [nativeGap095Scale]
  have hs := native_individual_scaled_source_row 95 k nativeGap095Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap095Scale hz hk
  dsimp only at hs
  rw [nativeGap095Coefficients_formula, nativeGap095System_formula] at hs
  exact hs

theorem native_gap096_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap096System
    let c := nativeIndividualRow 96 (k+1) (nativeOld 96)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 96 = nativeGap096Old := by
    unfold nativeOld
    rw [nativeGap096Raw_formula]
    exact nativeGap096Old_formula
  rw [ho]
  have hz : nativeGap096Scale ≠ 0 := by norm_num [nativeGap096Scale]
  have hs := native_individual_scaled_source_row 96 k nativeGap096Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap096Scale hz hk
  dsimp only at hs
  rw [nativeGap096Coefficients_formula, nativeGap096System_formula] at hs
  exact hs

theorem native_gap097_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap097System
    let c := nativeIndividualRow 97 (k+1) (nativeOld 97)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 97 = nativeGap097Old := by
    unfold nativeOld
    rw [nativeGap097Raw_formula]
    exact nativeGap097Old_formula
  rw [ho]
  have hz : nativeGap097Scale ≠ 0 := by norm_num [nativeGap097Scale]
  have hs := native_individual_scaled_source_row 97 k nativeGap097Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap097Scale hz hk
  dsimp only at hs
  rw [nativeGap097Coefficients_formula, nativeGap097System_formula] at hs
  exact hs

theorem native_gap098_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap098System
    let c := nativeIndividualRow 98 (k+1) (nativeOld 98)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 98 = nativeGap098Old := by
    unfold nativeOld
    rw [nativeGap098Raw_formula]
    exact nativeGap098Old_formula
  rw [ho]
  have hz : nativeGap098Scale ≠ 0 := by norm_num [nativeGap098Scale]
  have hs := native_individual_scaled_source_row 98 k nativeGap098Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap098Scale hz hk
  dsimp only at hs
  rw [nativeGap098Coefficients_formula, nativeGap098System_formula] at hs
  exact hs

theorem native_gap099_source_row (k : ℕ) (hk : k < 20) :
    let s := nativeGap099System
    let c := nativeIndividualRow 99 (k+1) (nativeOld 99)
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*s.z = c.1 ∧
    s.force.getD (k+1) 0*s.z^(k+1) = c.2.2 := by
  have ho : nativeOld 99 = nativeGap099Old := by
    unfold nativeOld
    rw [nativeGap099Raw_formula]
    exact nativeGap099Old_formula
  rw [ho]
  have hz : nativeGap099Scale ≠ 0 := by norm_num [nativeGap099Scale]
  have hs := native_individual_scaled_source_row 99 k nativeGap099Old
    (747710019334041416999114505700155678014915011007411709157812696885089918341076187469632793/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) nativeGap099Scale hz hk
  dsimp only at hs
  rw [nativeGap099Coefficients_formula, nativeGap099System_formula] at hs
  exact hs

end ASDExplicitGamma.Native
