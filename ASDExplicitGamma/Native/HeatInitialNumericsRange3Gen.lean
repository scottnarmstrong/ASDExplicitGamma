module

public import ASDExplicitGamma.Native.HeatInitialNumericsDataGen
public import ASDExplicitGamma.Numerics.Native.Heat047Initial
public import ASDExplicitGamma.Numerics.Native.Heat048Initial
public import ASDExplicitGamma.Numerics.Native.Heat049Initial
public import ASDExplicitGamma.Numerics.Native.Heat050Initial
public import ASDExplicitGamma.Numerics.Native.Heat051Initial
public import ASDExplicitGamma.Numerics.Native.Heat052Initial
public import ASDExplicitGamma.Numerics.Native.Heat053Initial
public import ASDExplicitGamma.Numerics.Native.Heat054Initial
public import ASDExplicitGamma.Numerics.Native.Heat055Initial
public import ASDExplicitGamma.Numerics.Native.Heat056Initial
public import ASDExplicitGamma.Numerics.Native.Heat057Initial
public import ASDExplicitGamma.Numerics.Native.Heat058Initial
public import ASDExplicitGamma.Numerics.Native.Heat059Initial
public import ASDExplicitGamma.Numerics.Native.Heat060Initial
public import ASDExplicitGamma.Numerics.Native.Heat061Initial
public import ASDExplicitGamma.Numerics.Native.Heat062Initial
public import ASDExplicitGamma.Numerics.Native.Heat063Initial
public import ASDExplicitGamma.Numerics.Native.Heat064Initial
public import ASDExplicitGamma.Numerics.Native.Heat065Initial

/-! Numeric certificates of the `ns`-shell refined initial moment for `47 ≤ ns < 66`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

theorem nativeHeat047BaseOk_Gen : nativeHeatGenBaseOk nativeHeat047Qm = true := by
  decide +kernel

theorem nativeHeat047RootOk_Gen : nativeHeatGenRootOk nativeHeat047Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_47_Gen : NativeHeatGenNum 47 := by
  refine nativeHeatGenNum_of_data 47 (by norm_num) nativeGap048Old ?_
    nativeHeat047Variance nativeHeat047Spectral nativeHeat047Qm
    nativeHeat047Variance_formula nativeHeat047Qm_formula ?_ ?_ ?_ ?_
    nativeHeat047BaseOk_Gen nativeHeat047RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap048Old]
  · norm_num [nativeHeat047Variance]
  · norm_num [nativeHeat047Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat047Qm]

theorem nativeHeat048BaseOk_Gen : nativeHeatGenBaseOk nativeHeat048Qm = true := by
  decide +kernel

theorem nativeHeat048RootOk_Gen : nativeHeatGenRootOk nativeHeat048Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_48_Gen : NativeHeatGenNum 48 := by
  refine nativeHeatGenNum_of_data 48 (by norm_num) nativeGap049Old ?_
    nativeHeat048Variance nativeHeat048Spectral nativeHeat048Qm
    nativeHeat048Variance_formula nativeHeat048Qm_formula ?_ ?_ ?_ ?_
    nativeHeat048BaseOk_Gen nativeHeat048RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap049Old]
  · norm_num [nativeHeat048Variance]
  · norm_num [nativeHeat048Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat048Qm]

theorem nativeHeat049BaseOk_Gen : nativeHeatGenBaseOk nativeHeat049Qm = true := by
  decide +kernel

theorem nativeHeat049RootOk_Gen : nativeHeatGenRootOk nativeHeat049Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_49_Gen : NativeHeatGenNum 49 := by
  refine nativeHeatGenNum_of_data 49 (by norm_num) nativeGap050Old ?_
    nativeHeat049Variance nativeHeat049Spectral nativeHeat049Qm
    nativeHeat049Variance_formula nativeHeat049Qm_formula ?_ ?_ ?_ ?_
    nativeHeat049BaseOk_Gen nativeHeat049RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap050Old]
  · norm_num [nativeHeat049Variance]
  · norm_num [nativeHeat049Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat049Qm]

theorem nativeHeat050BaseOk_Gen : nativeHeatGenBaseOk nativeHeat050Qm = true := by
  decide +kernel

theorem nativeHeat050RootOk_Gen : nativeHeatGenRootOk nativeHeat050Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_50_Gen : NativeHeatGenNum 50 := by
  refine nativeHeatGenNum_of_data 50 (by norm_num) nativeGap051Old ?_
    nativeHeat050Variance nativeHeat050Spectral nativeHeat050Qm
    nativeHeat050Variance_formula nativeHeat050Qm_formula ?_ ?_ ?_ ?_
    nativeHeat050BaseOk_Gen nativeHeat050RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap051Old]
  · norm_num [nativeHeat050Variance]
  · norm_num [nativeHeat050Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat050Qm]

theorem nativeHeat051BaseOk_Gen : nativeHeatGenBaseOk nativeHeat051Qm = true := by
  decide +kernel

theorem nativeHeat051RootOk_Gen : nativeHeatGenRootOk nativeHeat051Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_51_Gen : NativeHeatGenNum 51 := by
  refine nativeHeatGenNum_of_data 51 (by norm_num) nativeGap052Old ?_
    nativeHeat051Variance nativeHeat051Spectral nativeHeat051Qm
    nativeHeat051Variance_formula nativeHeat051Qm_formula ?_ ?_ ?_ ?_
    nativeHeat051BaseOk_Gen nativeHeat051RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap052Old]
  · norm_num [nativeHeat051Variance]
  · norm_num [nativeHeat051Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat051Qm]

theorem nativeHeat052BaseOk_Gen : nativeHeatGenBaseOk nativeHeat052Qm = true := by
  decide +kernel

theorem nativeHeat052RootOk_Gen : nativeHeatGenRootOk nativeHeat052Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_52_Gen : NativeHeatGenNum 52 := by
  refine nativeHeatGenNum_of_data 52 (by norm_num) nativeGap053Old ?_
    nativeHeat052Variance nativeHeat052Spectral nativeHeat052Qm
    nativeHeat052Variance_formula nativeHeat052Qm_formula ?_ ?_ ?_ ?_
    nativeHeat052BaseOk_Gen nativeHeat052RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap053Old]
  · norm_num [nativeHeat052Variance]
  · norm_num [nativeHeat052Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat052Qm]

theorem nativeHeat053BaseOk_Gen : nativeHeatGenBaseOk nativeHeat053Qm = true := by
  decide +kernel

theorem nativeHeat053RootOk_Gen : nativeHeatGenRootOk nativeHeat053Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_53_Gen : NativeHeatGenNum 53 := by
  refine nativeHeatGenNum_of_data 53 (by norm_num) nativeGap054Old ?_
    nativeHeat053Variance nativeHeat053Spectral nativeHeat053Qm
    nativeHeat053Variance_formula nativeHeat053Qm_formula ?_ ?_ ?_ ?_
    nativeHeat053BaseOk_Gen nativeHeat053RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap054Old]
  · norm_num [nativeHeat053Variance]
  · norm_num [nativeHeat053Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat053Qm]

theorem nativeHeat054BaseOk_Gen : nativeHeatGenBaseOk nativeHeat054Qm = true := by
  decide +kernel

theorem nativeHeat054RootOk_Gen : nativeHeatGenRootOk nativeHeat054Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_54_Gen : NativeHeatGenNum 54 := by
  refine nativeHeatGenNum_of_data 54 (by norm_num) nativeGap055Old ?_
    nativeHeat054Variance nativeHeat054Spectral nativeHeat054Qm
    nativeHeat054Variance_formula nativeHeat054Qm_formula ?_ ?_ ?_ ?_
    nativeHeat054BaseOk_Gen nativeHeat054RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap055Old]
  · norm_num [nativeHeat054Variance]
  · norm_num [nativeHeat054Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat054Qm]

theorem nativeHeat055BaseOk_Gen : nativeHeatGenBaseOk nativeHeat055Qm = true := by
  decide +kernel

theorem nativeHeat055RootOk_Gen : nativeHeatGenRootOk nativeHeat055Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_55_Gen : NativeHeatGenNum 55 := by
  refine nativeHeatGenNum_of_data 55 (by norm_num) nativeGap056Old ?_
    nativeHeat055Variance nativeHeat055Spectral nativeHeat055Qm
    nativeHeat055Variance_formula nativeHeat055Qm_formula ?_ ?_ ?_ ?_
    nativeHeat055BaseOk_Gen nativeHeat055RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap056Old]
  · norm_num [nativeHeat055Variance]
  · norm_num [nativeHeat055Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat055Qm]

theorem nativeHeat056BaseOk_Gen : nativeHeatGenBaseOk nativeHeat056Qm = true := by
  decide +kernel

theorem nativeHeat056RootOk_Gen : nativeHeatGenRootOk nativeHeat056Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_56_Gen : NativeHeatGenNum 56 := by
  refine nativeHeatGenNum_of_data 56 (by norm_num) nativeGap057Old ?_
    nativeHeat056Variance nativeHeat056Spectral nativeHeat056Qm
    nativeHeat056Variance_formula nativeHeat056Qm_formula ?_ ?_ ?_ ?_
    nativeHeat056BaseOk_Gen nativeHeat056RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap057Old]
  · norm_num [nativeHeat056Variance]
  · norm_num [nativeHeat056Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat056Qm]

theorem nativeHeat057BaseOk_Gen : nativeHeatGenBaseOk nativeHeat057Qm = true := by
  decide +kernel

theorem nativeHeat057RootOk_Gen : nativeHeatGenRootOk nativeHeat057Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_57_Gen : NativeHeatGenNum 57 := by
  refine nativeHeatGenNum_of_data 57 (by norm_num) nativeGap058Old ?_
    nativeHeat057Variance nativeHeat057Spectral nativeHeat057Qm
    nativeHeat057Variance_formula nativeHeat057Qm_formula ?_ ?_ ?_ ?_
    nativeHeat057BaseOk_Gen nativeHeat057RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap058Old]
  · norm_num [nativeHeat057Variance]
  · norm_num [nativeHeat057Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat057Qm]

theorem nativeHeat058BaseOk_Gen : nativeHeatGenBaseOk nativeHeat058Qm = true := by
  decide +kernel

theorem nativeHeat058RootOk_Gen : nativeHeatGenRootOk nativeHeat058Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_58_Gen : NativeHeatGenNum 58 := by
  refine nativeHeatGenNum_of_data 58 (by norm_num) nativeGap059Old ?_
    nativeHeat058Variance nativeHeat058Spectral nativeHeat058Qm
    nativeHeat058Variance_formula nativeHeat058Qm_formula ?_ ?_ ?_ ?_
    nativeHeat058BaseOk_Gen nativeHeat058RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap059Old]
  · norm_num [nativeHeat058Variance]
  · norm_num [nativeHeat058Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat058Qm]

theorem nativeHeat059BaseOk_Gen : nativeHeatGenBaseOk nativeHeat059Qm = true := by
  decide +kernel

theorem nativeHeat059RootOk_Gen : nativeHeatGenRootOk nativeHeat059Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_59_Gen : NativeHeatGenNum 59 := by
  refine nativeHeatGenNum_of_data 59 (by norm_num) nativeGap060Old ?_
    nativeHeat059Variance nativeHeat059Spectral nativeHeat059Qm
    nativeHeat059Variance_formula nativeHeat059Qm_formula ?_ ?_ ?_ ?_
    nativeHeat059BaseOk_Gen nativeHeat059RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap060Old]
  · norm_num [nativeHeat059Variance]
  · norm_num [nativeHeat059Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat059Qm]

theorem nativeHeat060BaseOk_Gen : nativeHeatGenBaseOk nativeHeat060Qm = true := by
  decide +kernel

theorem nativeHeat060RootOk_Gen : nativeHeatGenRootOk nativeHeat060Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_60_Gen : NativeHeatGenNum 60 := by
  refine nativeHeatGenNum_of_data 60 (by norm_num) nativeGap061Old ?_
    nativeHeat060Variance nativeHeat060Spectral nativeHeat060Qm
    nativeHeat060Variance_formula nativeHeat060Qm_formula ?_ ?_ ?_ ?_
    nativeHeat060BaseOk_Gen nativeHeat060RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap061Old]
  · norm_num [nativeHeat060Variance]
  · norm_num [nativeHeat060Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat060Qm]

theorem nativeHeat061BaseOk_Gen : nativeHeatGenBaseOk nativeHeat061Qm = true := by
  decide +kernel

theorem nativeHeat061RootOk_Gen : nativeHeatGenRootOk nativeHeat061Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_61_Gen : NativeHeatGenNum 61 := by
  refine nativeHeatGenNum_of_data 61 (by norm_num) nativeGap062Old ?_
    nativeHeat061Variance nativeHeat061Spectral nativeHeat061Qm
    nativeHeat061Variance_formula nativeHeat061Qm_formula ?_ ?_ ?_ ?_
    nativeHeat061BaseOk_Gen nativeHeat061RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap062Old]
  · norm_num [nativeHeat061Variance]
  · norm_num [nativeHeat061Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat061Qm]

theorem nativeHeat062BaseOk_Gen : nativeHeatGenBaseOk nativeHeat062Qm = true := by
  decide +kernel

theorem nativeHeat062RootOk_Gen : nativeHeatGenRootOk nativeHeat062Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_62_Gen : NativeHeatGenNum 62 := by
  refine nativeHeatGenNum_of_data 62 (by norm_num) nativeGap063Old ?_
    nativeHeat062Variance nativeHeat062Spectral nativeHeat062Qm
    nativeHeat062Variance_formula nativeHeat062Qm_formula ?_ ?_ ?_ ?_
    nativeHeat062BaseOk_Gen nativeHeat062RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap063Old]
  · norm_num [nativeHeat062Variance]
  · norm_num [nativeHeat062Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat062Qm]

theorem nativeHeat063BaseOk_Gen : nativeHeatGenBaseOk nativeHeat063Qm = true := by
  decide +kernel

theorem nativeHeat063RootOk_Gen : nativeHeatGenRootOk nativeHeat063Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_63_Gen : NativeHeatGenNum 63 := by
  refine nativeHeatGenNum_of_data 63 (by norm_num) nativeGap064Old ?_
    nativeHeat063Variance nativeHeat063Spectral nativeHeat063Qm
    nativeHeat063Variance_formula nativeHeat063Qm_formula ?_ ?_ ?_ ?_
    nativeHeat063BaseOk_Gen nativeHeat063RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap064Old]
  · norm_num [nativeHeat063Variance]
  · norm_num [nativeHeat063Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat063Qm]

theorem nativeHeat064BaseOk_Gen : nativeHeatGenBaseOk nativeHeat064Qm = true := by
  decide +kernel

theorem nativeHeat064RootOk_Gen : nativeHeatGenRootOk nativeHeat064Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_64_Gen : NativeHeatGenNum 64 := by
  refine nativeHeatGenNum_of_data 64 (by norm_num) nativeGap065Old ?_
    nativeHeat064Variance nativeHeat064Spectral nativeHeat064Qm
    nativeHeat064Variance_formula nativeHeat064Qm_formula ?_ ?_ ?_ ?_
    nativeHeat064BaseOk_Gen nativeHeat064RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap065Old]
  · norm_num [nativeHeat064Variance]
  · norm_num [nativeHeat064Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat064Qm]

theorem nativeHeat065BaseOk_Gen : nativeHeatGenBaseOk nativeHeat065Qm = true := by
  decide +kernel

theorem nativeHeat065RootOk_Gen : nativeHeatGenRootOk nativeHeat065Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_65_Gen : NativeHeatGenNum 65 := by
  refine nativeHeatGenNum_of_data 65 (by norm_num) nativeGap066Old ?_
    nativeHeat065Variance nativeHeat065Spectral nativeHeat065Qm
    nativeHeat065Variance_formula nativeHeat065Qm_formula ?_ ?_ ?_ ?_
    nativeHeat065BaseOk_Gen nativeHeat065RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap066Old]
  · norm_num [nativeHeat065Variance]
  · norm_num [nativeHeat065Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat065Qm]

theorem nativeHeatGenNum_range3_Gen (ns : ℕ) (h1 : 47 ≤ ns) (h2 : ns < 66) :
    NativeHeatGenNum ns := by
  by_cases hh47 : ns = 47
  · subst hh47; exact nativeHeatGenNum_47_Gen
  by_cases hh48 : ns = 48
  · subst hh48; exact nativeHeatGenNum_48_Gen
  by_cases hh49 : ns = 49
  · subst hh49; exact nativeHeatGenNum_49_Gen
  by_cases hh50 : ns = 50
  · subst hh50; exact nativeHeatGenNum_50_Gen
  by_cases hh51 : ns = 51
  · subst hh51; exact nativeHeatGenNum_51_Gen
  by_cases hh52 : ns = 52
  · subst hh52; exact nativeHeatGenNum_52_Gen
  by_cases hh53 : ns = 53
  · subst hh53; exact nativeHeatGenNum_53_Gen
  by_cases hh54 : ns = 54
  · subst hh54; exact nativeHeatGenNum_54_Gen
  by_cases hh55 : ns = 55
  · subst hh55; exact nativeHeatGenNum_55_Gen
  by_cases hh56 : ns = 56
  · subst hh56; exact nativeHeatGenNum_56_Gen
  by_cases hh57 : ns = 57
  · subst hh57; exact nativeHeatGenNum_57_Gen
  by_cases hh58 : ns = 58
  · subst hh58; exact nativeHeatGenNum_58_Gen
  by_cases hh59 : ns = 59
  · subst hh59; exact nativeHeatGenNum_59_Gen
  by_cases hh60 : ns = 60
  · subst hh60; exact nativeHeatGenNum_60_Gen
  by_cases hh61 : ns = 61
  · subst hh61; exact nativeHeatGenNum_61_Gen
  by_cases hh62 : ns = 62
  · subst hh62; exact nativeHeatGenNum_62_Gen
  by_cases hh63 : ns = 63
  · subst hh63; exact nativeHeatGenNum_63_Gen
  by_cases hh64 : ns = 64
  · subst hh64; exact nativeHeatGenNum_64_Gen
  have hh : ns = 65 := by omega
  subst hh; exact nativeHeatGenNum_65_Gen

end ASDExplicitGamma.Native
