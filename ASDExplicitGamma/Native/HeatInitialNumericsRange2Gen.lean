module

public import ASDExplicitGamma.Native.HeatInitialNumericsDataGen
public import ASDExplicitGamma.Numerics.Native.Heat028Initial
public import ASDExplicitGamma.Numerics.Native.Heat029Initial
public import ASDExplicitGamma.Numerics.Native.Heat030Initial
public import ASDExplicitGamma.Numerics.Native.Heat031Initial
public import ASDExplicitGamma.Numerics.Native.Heat032Initial
public import ASDExplicitGamma.Numerics.Native.Heat033Initial
public import ASDExplicitGamma.Numerics.Native.Heat034Initial
public import ASDExplicitGamma.Numerics.Native.Heat035Initial
public import ASDExplicitGamma.Numerics.Native.Heat036Initial
public import ASDExplicitGamma.Numerics.Native.Heat037Initial
public import ASDExplicitGamma.Numerics.Native.Heat038Initial
public import ASDExplicitGamma.Numerics.Native.Heat039Initial
public import ASDExplicitGamma.Numerics.Native.Heat040Initial
public import ASDExplicitGamma.Numerics.Native.Heat041Initial
public import ASDExplicitGamma.Numerics.Native.Heat042Initial
public import ASDExplicitGamma.Numerics.Native.Heat043Initial
public import ASDExplicitGamma.Numerics.Native.Heat044Initial
public import ASDExplicitGamma.Numerics.Native.Heat045Initial
public import ASDExplicitGamma.Numerics.Native.Heat046Initial

/-! Numeric certificates of the `ns`-shell refined initial moment for `28 ≤ ns < 47`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

theorem nativeHeat028BaseOk_Gen : nativeHeatGenBaseOk nativeHeat028Qm = true := by
  decide +kernel

theorem nativeHeat028RootOk_Gen : nativeHeatGenRootOk nativeHeat028Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_28_Gen : NativeHeatGenNum 28 := by
  refine nativeHeatGenNum_of_data 28 (by norm_num) nativeGap029Old ?_
    nativeHeat028Variance nativeHeat028Spectral nativeHeat028Qm
    nativeHeat028Variance_formula nativeHeat028Qm_formula ?_ ?_ ?_ ?_
    nativeHeat028BaseOk_Gen nativeHeat028RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap029Old]
  · norm_num [nativeHeat028Variance]
  · norm_num [nativeHeat028Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat028Qm]

theorem nativeHeat029BaseOk_Gen : nativeHeatGenBaseOk nativeHeat029Qm = true := by
  decide +kernel

theorem nativeHeat029RootOk_Gen : nativeHeatGenRootOk nativeHeat029Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_29_Gen : NativeHeatGenNum 29 := by
  refine nativeHeatGenNum_of_data 29 (by norm_num) nativeGap030Old ?_
    nativeHeat029Variance nativeHeat029Spectral nativeHeat029Qm
    nativeHeat029Variance_formula nativeHeat029Qm_formula ?_ ?_ ?_ ?_
    nativeHeat029BaseOk_Gen nativeHeat029RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap030Old]
  · norm_num [nativeHeat029Variance]
  · norm_num [nativeHeat029Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat029Qm]

theorem nativeHeat030BaseOk_Gen : nativeHeatGenBaseOk nativeHeat030Qm = true := by
  decide +kernel

theorem nativeHeat030RootOk_Gen : nativeHeatGenRootOk nativeHeat030Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_30_Gen : NativeHeatGenNum 30 := by
  refine nativeHeatGenNum_of_data 30 (by norm_num) nativeGap031Old ?_
    nativeHeat030Variance nativeHeat030Spectral nativeHeat030Qm
    nativeHeat030Variance_formula nativeHeat030Qm_formula ?_ ?_ ?_ ?_
    nativeHeat030BaseOk_Gen nativeHeat030RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap031Old]
  · norm_num [nativeHeat030Variance]
  · norm_num [nativeHeat030Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat030Qm]

theorem nativeHeat031BaseOk_Gen : nativeHeatGenBaseOk nativeHeat031Qm = true := by
  decide +kernel

theorem nativeHeat031RootOk_Gen : nativeHeatGenRootOk nativeHeat031Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_31_Gen : NativeHeatGenNum 31 := by
  refine nativeHeatGenNum_of_data 31 (by norm_num) nativeGap032Old ?_
    nativeHeat031Variance nativeHeat031Spectral nativeHeat031Qm
    nativeHeat031Variance_formula nativeHeat031Qm_formula ?_ ?_ ?_ ?_
    nativeHeat031BaseOk_Gen nativeHeat031RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap032Old]
  · norm_num [nativeHeat031Variance]
  · norm_num [nativeHeat031Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat031Qm]

theorem nativeHeat032BaseOk_Gen : nativeHeatGenBaseOk nativeHeat032Qm = true := by
  decide +kernel

theorem nativeHeat032RootOk_Gen : nativeHeatGenRootOk nativeHeat032Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_32_Gen : NativeHeatGenNum 32 := by
  refine nativeHeatGenNum_of_data 32 (by norm_num) nativeGap033Old ?_
    nativeHeat032Variance nativeHeat032Spectral nativeHeat032Qm
    nativeHeat032Variance_formula nativeHeat032Qm_formula ?_ ?_ ?_ ?_
    nativeHeat032BaseOk_Gen nativeHeat032RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap033Old]
  · norm_num [nativeHeat032Variance]
  · norm_num [nativeHeat032Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat032Qm]

theorem nativeHeat033BaseOk_Gen : nativeHeatGenBaseOk nativeHeat033Qm = true := by
  decide +kernel

theorem nativeHeat033RootOk_Gen : nativeHeatGenRootOk nativeHeat033Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_33_Gen : NativeHeatGenNum 33 := by
  refine nativeHeatGenNum_of_data 33 (by norm_num) nativeGap034Old ?_
    nativeHeat033Variance nativeHeat033Spectral nativeHeat033Qm
    nativeHeat033Variance_formula nativeHeat033Qm_formula ?_ ?_ ?_ ?_
    nativeHeat033BaseOk_Gen nativeHeat033RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap034Old]
  · norm_num [nativeHeat033Variance]
  · norm_num [nativeHeat033Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat033Qm]

theorem nativeHeat034BaseOk_Gen : nativeHeatGenBaseOk nativeHeat034Qm = true := by
  decide +kernel

theorem nativeHeat034RootOk_Gen : nativeHeatGenRootOk nativeHeat034Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_34_Gen : NativeHeatGenNum 34 := by
  refine nativeHeatGenNum_of_data 34 (by norm_num) nativeGap035Old ?_
    nativeHeat034Variance nativeHeat034Spectral nativeHeat034Qm
    nativeHeat034Variance_formula nativeHeat034Qm_formula ?_ ?_ ?_ ?_
    nativeHeat034BaseOk_Gen nativeHeat034RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap035Old]
  · norm_num [nativeHeat034Variance]
  · norm_num [nativeHeat034Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat034Qm]

theorem nativeHeat035BaseOk_Gen : nativeHeatGenBaseOk nativeHeat035Qm = true := by
  decide +kernel

theorem nativeHeat035RootOk_Gen : nativeHeatGenRootOk nativeHeat035Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_35_Gen : NativeHeatGenNum 35 := by
  refine nativeHeatGenNum_of_data 35 (by norm_num) nativeGap036Old ?_
    nativeHeat035Variance nativeHeat035Spectral nativeHeat035Qm
    nativeHeat035Variance_formula nativeHeat035Qm_formula ?_ ?_ ?_ ?_
    nativeHeat035BaseOk_Gen nativeHeat035RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap036Old]
  · norm_num [nativeHeat035Variance]
  · norm_num [nativeHeat035Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat035Qm]

theorem nativeHeat036BaseOk_Gen : nativeHeatGenBaseOk nativeHeat036Qm = true := by
  decide +kernel

theorem nativeHeat036RootOk_Gen : nativeHeatGenRootOk nativeHeat036Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_36_Gen : NativeHeatGenNum 36 := by
  refine nativeHeatGenNum_of_data 36 (by norm_num) nativeGap037Old ?_
    nativeHeat036Variance nativeHeat036Spectral nativeHeat036Qm
    nativeHeat036Variance_formula nativeHeat036Qm_formula ?_ ?_ ?_ ?_
    nativeHeat036BaseOk_Gen nativeHeat036RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap037Old]
  · norm_num [nativeHeat036Variance]
  · norm_num [nativeHeat036Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat036Qm]

theorem nativeHeat037BaseOk_Gen : nativeHeatGenBaseOk nativeHeat037Qm = true := by
  decide +kernel

theorem nativeHeat037RootOk_Gen : nativeHeatGenRootOk nativeHeat037Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_37_Gen : NativeHeatGenNum 37 := by
  refine nativeHeatGenNum_of_data 37 (by norm_num) nativeGap038Old ?_
    nativeHeat037Variance nativeHeat037Spectral nativeHeat037Qm
    nativeHeat037Variance_formula nativeHeat037Qm_formula ?_ ?_ ?_ ?_
    nativeHeat037BaseOk_Gen nativeHeat037RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap038Old]
  · norm_num [nativeHeat037Variance]
  · norm_num [nativeHeat037Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat037Qm]

theorem nativeHeat038BaseOk_Gen : nativeHeatGenBaseOk nativeHeat038Qm = true := by
  decide +kernel

theorem nativeHeat038RootOk_Gen : nativeHeatGenRootOk nativeHeat038Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_38_Gen : NativeHeatGenNum 38 := by
  refine nativeHeatGenNum_of_data 38 (by norm_num) nativeGap039Old ?_
    nativeHeat038Variance nativeHeat038Spectral nativeHeat038Qm
    nativeHeat038Variance_formula nativeHeat038Qm_formula ?_ ?_ ?_ ?_
    nativeHeat038BaseOk_Gen nativeHeat038RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap039Old]
  · norm_num [nativeHeat038Variance]
  · norm_num [nativeHeat038Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat038Qm]

theorem nativeHeat039BaseOk_Gen : nativeHeatGenBaseOk nativeHeat039Qm = true := by
  decide +kernel

theorem nativeHeat039RootOk_Gen : nativeHeatGenRootOk nativeHeat039Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_39_Gen : NativeHeatGenNum 39 := by
  refine nativeHeatGenNum_of_data 39 (by norm_num) nativeGap040Old ?_
    nativeHeat039Variance nativeHeat039Spectral nativeHeat039Qm
    nativeHeat039Variance_formula nativeHeat039Qm_formula ?_ ?_ ?_ ?_
    nativeHeat039BaseOk_Gen nativeHeat039RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap040Old]
  · norm_num [nativeHeat039Variance]
  · norm_num [nativeHeat039Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat039Qm]

theorem nativeHeat040BaseOk_Gen : nativeHeatGenBaseOk nativeHeat040Qm = true := by
  decide +kernel

theorem nativeHeat040RootOk_Gen : nativeHeatGenRootOk nativeHeat040Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_40_Gen : NativeHeatGenNum 40 := by
  refine nativeHeatGenNum_of_data 40 (by norm_num) nativeGap041Old ?_
    nativeHeat040Variance nativeHeat040Spectral nativeHeat040Qm
    nativeHeat040Variance_formula nativeHeat040Qm_formula ?_ ?_ ?_ ?_
    nativeHeat040BaseOk_Gen nativeHeat040RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap041Old]
  · norm_num [nativeHeat040Variance]
  · norm_num [nativeHeat040Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat040Qm]

theorem nativeHeat041BaseOk_Gen : nativeHeatGenBaseOk nativeHeat041Qm = true := by
  decide +kernel

theorem nativeHeat041RootOk_Gen : nativeHeatGenRootOk nativeHeat041Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_41_Gen : NativeHeatGenNum 41 := by
  refine nativeHeatGenNum_of_data 41 (by norm_num) nativeGap042Old ?_
    nativeHeat041Variance nativeHeat041Spectral nativeHeat041Qm
    nativeHeat041Variance_formula nativeHeat041Qm_formula ?_ ?_ ?_ ?_
    nativeHeat041BaseOk_Gen nativeHeat041RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap042Old]
  · norm_num [nativeHeat041Variance]
  · norm_num [nativeHeat041Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat041Qm]

theorem nativeHeat042BaseOk_Gen : nativeHeatGenBaseOk nativeHeat042Qm = true := by
  decide +kernel

theorem nativeHeat042RootOk_Gen : nativeHeatGenRootOk nativeHeat042Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_42_Gen : NativeHeatGenNum 42 := by
  refine nativeHeatGenNum_of_data 42 (by norm_num) nativeGap043Old ?_
    nativeHeat042Variance nativeHeat042Spectral nativeHeat042Qm
    nativeHeat042Variance_formula nativeHeat042Qm_formula ?_ ?_ ?_ ?_
    nativeHeat042BaseOk_Gen nativeHeat042RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap043Old]
  · norm_num [nativeHeat042Variance]
  · norm_num [nativeHeat042Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat042Qm]

theorem nativeHeat043BaseOk_Gen : nativeHeatGenBaseOk nativeHeat043Qm = true := by
  decide +kernel

theorem nativeHeat043RootOk_Gen : nativeHeatGenRootOk nativeHeat043Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_43_Gen : NativeHeatGenNum 43 := by
  refine nativeHeatGenNum_of_data 43 (by norm_num) nativeGap044Old ?_
    nativeHeat043Variance nativeHeat043Spectral nativeHeat043Qm
    nativeHeat043Variance_formula nativeHeat043Qm_formula ?_ ?_ ?_ ?_
    nativeHeat043BaseOk_Gen nativeHeat043RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap044Old]
  · norm_num [nativeHeat043Variance]
  · norm_num [nativeHeat043Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat043Qm]

theorem nativeHeat044BaseOk_Gen : nativeHeatGenBaseOk nativeHeat044Qm = true := by
  decide +kernel

theorem nativeHeat044RootOk_Gen : nativeHeatGenRootOk nativeHeat044Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_44_Gen : NativeHeatGenNum 44 := by
  refine nativeHeatGenNum_of_data 44 (by norm_num) nativeGap045Old ?_
    nativeHeat044Variance nativeHeat044Spectral nativeHeat044Qm
    nativeHeat044Variance_formula nativeHeat044Qm_formula ?_ ?_ ?_ ?_
    nativeHeat044BaseOk_Gen nativeHeat044RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap045Old]
  · norm_num [nativeHeat044Variance]
  · norm_num [nativeHeat044Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat044Qm]

theorem nativeHeat045BaseOk_Gen : nativeHeatGenBaseOk nativeHeat045Qm = true := by
  decide +kernel

theorem nativeHeat045RootOk_Gen : nativeHeatGenRootOk nativeHeat045Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_45_Gen : NativeHeatGenNum 45 := by
  refine nativeHeatGenNum_of_data 45 (by norm_num) nativeGap046Old ?_
    nativeHeat045Variance nativeHeat045Spectral nativeHeat045Qm
    nativeHeat045Variance_formula nativeHeat045Qm_formula ?_ ?_ ?_ ?_
    nativeHeat045BaseOk_Gen nativeHeat045RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap046Old]
  · norm_num [nativeHeat045Variance]
  · norm_num [nativeHeat045Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat045Qm]

theorem nativeHeat046BaseOk_Gen : nativeHeatGenBaseOk nativeHeat046Qm = true := by
  decide +kernel

theorem nativeHeat046RootOk_Gen : nativeHeatGenRootOk nativeHeat046Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_46_Gen : NativeHeatGenNum 46 := by
  refine nativeHeatGenNum_of_data 46 (by norm_num) nativeGap047Old ?_
    nativeHeat046Variance nativeHeat046Spectral nativeHeat046Qm
    nativeHeat046Variance_formula nativeHeat046Qm_formula ?_ ?_ ?_ ?_
    nativeHeat046BaseOk_Gen nativeHeat046RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap047Old]
  · norm_num [nativeHeat046Variance]
  · norm_num [nativeHeat046Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat046Qm]

theorem nativeHeatGenNum_range2_Gen (ns : ℕ) (h1 : 28 ≤ ns) (h2 : ns < 47) :
    NativeHeatGenNum ns := by
  by_cases hh28 : ns = 28
  · subst hh28; exact nativeHeatGenNum_28_Gen
  by_cases hh29 : ns = 29
  · subst hh29; exact nativeHeatGenNum_29_Gen
  by_cases hh30 : ns = 30
  · subst hh30; exact nativeHeatGenNum_30_Gen
  by_cases hh31 : ns = 31
  · subst hh31; exact nativeHeatGenNum_31_Gen
  by_cases hh32 : ns = 32
  · subst hh32; exact nativeHeatGenNum_32_Gen
  by_cases hh33 : ns = 33
  · subst hh33; exact nativeHeatGenNum_33_Gen
  by_cases hh34 : ns = 34
  · subst hh34; exact nativeHeatGenNum_34_Gen
  by_cases hh35 : ns = 35
  · subst hh35; exact nativeHeatGenNum_35_Gen
  by_cases hh36 : ns = 36
  · subst hh36; exact nativeHeatGenNum_36_Gen
  by_cases hh37 : ns = 37
  · subst hh37; exact nativeHeatGenNum_37_Gen
  by_cases hh38 : ns = 38
  · subst hh38; exact nativeHeatGenNum_38_Gen
  by_cases hh39 : ns = 39
  · subst hh39; exact nativeHeatGenNum_39_Gen
  by_cases hh40 : ns = 40
  · subst hh40; exact nativeHeatGenNum_40_Gen
  by_cases hh41 : ns = 41
  · subst hh41; exact nativeHeatGenNum_41_Gen
  by_cases hh42 : ns = 42
  · subst hh42; exact nativeHeatGenNum_42_Gen
  by_cases hh43 : ns = 43
  · subst hh43; exact nativeHeatGenNum_43_Gen
  by_cases hh44 : ns = 44
  · subst hh44; exact nativeHeatGenNum_44_Gen
  by_cases hh45 : ns = 45
  · subst hh45; exact nativeHeatGenNum_45_Gen
  have hh : ns = 46 := by omega
  subst hh; exact nativeHeatGenNum_46_Gen

end ASDExplicitGamma.Native
