module

public import ASDExplicitGamma.Native.HeatInitialNumericsDataGen
public import ASDExplicitGamma.Numerics.Native.Heat066Initial
public import ASDExplicitGamma.Numerics.Native.Heat067Initial
public import ASDExplicitGamma.Numerics.Native.Heat068Initial
public import ASDExplicitGamma.Numerics.Native.Heat069Initial
public import ASDExplicitGamma.Numerics.Native.Heat070Initial
public import ASDExplicitGamma.Numerics.Native.Heat071Initial
public import ASDExplicitGamma.Numerics.Native.Heat072Initial
public import ASDExplicitGamma.Numerics.Native.Heat073Initial
public import ASDExplicitGamma.Numerics.Native.Heat074Initial
public import ASDExplicitGamma.Numerics.Native.Heat075Initial
public import ASDExplicitGamma.Numerics.Native.Heat076Initial
public import ASDExplicitGamma.Numerics.Native.Heat077Initial
public import ASDExplicitGamma.Numerics.Native.Heat078Initial
public import ASDExplicitGamma.Numerics.Native.Heat079Initial
public import ASDExplicitGamma.Numerics.Native.Heat080Initial
public import ASDExplicitGamma.Numerics.Native.Heat081Initial
public import ASDExplicitGamma.Numerics.Native.Heat082Initial
public import ASDExplicitGamma.Numerics.Native.Heat083Initial
public import ASDExplicitGamma.Numerics.Native.Heat084Initial

/-! Numeric certificates of the `ns`-shell refined initial moment for `66 ≤ ns < 85`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

theorem nativeHeat066BaseOk_Gen : nativeHeatGenBaseOk nativeHeat066Qm = true := by
  decide +kernel

theorem nativeHeat066RootOk_Gen : nativeHeatGenRootOk nativeHeat066Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_66_Gen : NativeHeatGenNum 66 := by
  refine nativeHeatGenNum_of_data 66 (by norm_num) nativeGap067Old ?_
    nativeHeat066Variance nativeHeat066Spectral nativeHeat066Qm
    nativeHeat066Variance_formula nativeHeat066Qm_formula ?_ ?_ ?_ ?_
    nativeHeat066BaseOk_Gen nativeHeat066RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap067Old]
  · norm_num [nativeHeat066Variance]
  · norm_num [nativeHeat066Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat066Qm]

theorem nativeHeat067BaseOk_Gen : nativeHeatGenBaseOk nativeHeat067Qm = true := by
  decide +kernel

theorem nativeHeat067RootOk_Gen : nativeHeatGenRootOk nativeHeat067Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_67_Gen : NativeHeatGenNum 67 := by
  refine nativeHeatGenNum_of_data 67 (by norm_num) nativeGap068Old ?_
    nativeHeat067Variance nativeHeat067Spectral nativeHeat067Qm
    nativeHeat067Variance_formula nativeHeat067Qm_formula ?_ ?_ ?_ ?_
    nativeHeat067BaseOk_Gen nativeHeat067RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap068Old]
  · norm_num [nativeHeat067Variance]
  · norm_num [nativeHeat067Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat067Qm]

theorem nativeHeat068BaseOk_Gen : nativeHeatGenBaseOk nativeHeat068Qm = true := by
  decide +kernel

theorem nativeHeat068RootOk_Gen : nativeHeatGenRootOk nativeHeat068Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_68_Gen : NativeHeatGenNum 68 := by
  refine nativeHeatGenNum_of_data 68 (by norm_num) nativeGap069Old ?_
    nativeHeat068Variance nativeHeat068Spectral nativeHeat068Qm
    nativeHeat068Variance_formula nativeHeat068Qm_formula ?_ ?_ ?_ ?_
    nativeHeat068BaseOk_Gen nativeHeat068RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap069Old]
  · norm_num [nativeHeat068Variance]
  · norm_num [nativeHeat068Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat068Qm]

theorem nativeHeat069BaseOk_Gen : nativeHeatGenBaseOk nativeHeat069Qm = true := by
  decide +kernel

theorem nativeHeat069RootOk_Gen : nativeHeatGenRootOk nativeHeat069Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_69_Gen : NativeHeatGenNum 69 := by
  refine nativeHeatGenNum_of_data 69 (by norm_num) nativeGap070Old ?_
    nativeHeat069Variance nativeHeat069Spectral nativeHeat069Qm
    nativeHeat069Variance_formula nativeHeat069Qm_formula ?_ ?_ ?_ ?_
    nativeHeat069BaseOk_Gen nativeHeat069RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap070Old]
  · norm_num [nativeHeat069Variance]
  · norm_num [nativeHeat069Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat069Qm]

theorem nativeHeat070BaseOk_Gen : nativeHeatGenBaseOk nativeHeat070Qm = true := by
  decide +kernel

theorem nativeHeat070RootOk_Gen : nativeHeatGenRootOk nativeHeat070Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_70_Gen : NativeHeatGenNum 70 := by
  refine nativeHeatGenNum_of_data 70 (by norm_num) nativeGap071Old ?_
    nativeHeat070Variance nativeHeat070Spectral nativeHeat070Qm
    nativeHeat070Variance_formula nativeHeat070Qm_formula ?_ ?_ ?_ ?_
    nativeHeat070BaseOk_Gen nativeHeat070RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap071Old]
  · norm_num [nativeHeat070Variance]
  · norm_num [nativeHeat070Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat070Qm]

theorem nativeHeat071BaseOk_Gen : nativeHeatGenBaseOk nativeHeat071Qm = true := by
  decide +kernel

theorem nativeHeat071RootOk_Gen : nativeHeatGenRootOk nativeHeat071Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_71_Gen : NativeHeatGenNum 71 := by
  refine nativeHeatGenNum_of_data 71 (by norm_num) nativeGap072Old ?_
    nativeHeat071Variance nativeHeat071Spectral nativeHeat071Qm
    nativeHeat071Variance_formula nativeHeat071Qm_formula ?_ ?_ ?_ ?_
    nativeHeat071BaseOk_Gen nativeHeat071RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap072Old]
  · norm_num [nativeHeat071Variance]
  · norm_num [nativeHeat071Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat071Qm]

theorem nativeHeat072BaseOk_Gen : nativeHeatGenBaseOk nativeHeat072Qm = true := by
  decide +kernel

theorem nativeHeat072RootOk_Gen : nativeHeatGenRootOk nativeHeat072Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_72_Gen : NativeHeatGenNum 72 := by
  refine nativeHeatGenNum_of_data 72 (by norm_num) nativeGap073Old ?_
    nativeHeat072Variance nativeHeat072Spectral nativeHeat072Qm
    nativeHeat072Variance_formula nativeHeat072Qm_formula ?_ ?_ ?_ ?_
    nativeHeat072BaseOk_Gen nativeHeat072RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap073Old]
  · norm_num [nativeHeat072Variance]
  · norm_num [nativeHeat072Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat072Qm]

theorem nativeHeat073BaseOk_Gen : nativeHeatGenBaseOk nativeHeat073Qm = true := by
  decide +kernel

theorem nativeHeat073RootOk_Gen : nativeHeatGenRootOk nativeHeat073Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_73_Gen : NativeHeatGenNum 73 := by
  refine nativeHeatGenNum_of_data 73 (by norm_num) nativeGap074Old ?_
    nativeHeat073Variance nativeHeat073Spectral nativeHeat073Qm
    nativeHeat073Variance_formula nativeHeat073Qm_formula ?_ ?_ ?_ ?_
    nativeHeat073BaseOk_Gen nativeHeat073RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap074Old]
  · norm_num [nativeHeat073Variance]
  · norm_num [nativeHeat073Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat073Qm]

theorem nativeHeat074BaseOk_Gen : nativeHeatGenBaseOk nativeHeat074Qm = true := by
  decide +kernel

theorem nativeHeat074RootOk_Gen : nativeHeatGenRootOk nativeHeat074Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_74_Gen : NativeHeatGenNum 74 := by
  refine nativeHeatGenNum_of_data 74 (by norm_num) nativeGap075Old ?_
    nativeHeat074Variance nativeHeat074Spectral nativeHeat074Qm
    nativeHeat074Variance_formula nativeHeat074Qm_formula ?_ ?_ ?_ ?_
    nativeHeat074BaseOk_Gen nativeHeat074RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap075Old]
  · norm_num [nativeHeat074Variance]
  · norm_num [nativeHeat074Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat074Qm]

theorem nativeHeat075BaseOk_Gen : nativeHeatGenBaseOk nativeHeat075Qm = true := by
  decide +kernel

theorem nativeHeat075RootOk_Gen : nativeHeatGenRootOk nativeHeat075Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_75_Gen : NativeHeatGenNum 75 := by
  refine nativeHeatGenNum_of_data 75 (by norm_num) nativeGap076Old ?_
    nativeHeat075Variance nativeHeat075Spectral nativeHeat075Qm
    nativeHeat075Variance_formula nativeHeat075Qm_formula ?_ ?_ ?_ ?_
    nativeHeat075BaseOk_Gen nativeHeat075RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap076Old]
  · norm_num [nativeHeat075Variance]
  · norm_num [nativeHeat075Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat075Qm]

theorem nativeHeat076BaseOk_Gen : nativeHeatGenBaseOk nativeHeat076Qm = true := by
  decide +kernel

theorem nativeHeat076RootOk_Gen : nativeHeatGenRootOk nativeHeat076Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_76_Gen : NativeHeatGenNum 76 := by
  refine nativeHeatGenNum_of_data 76 (by norm_num) nativeGap077Old ?_
    nativeHeat076Variance nativeHeat076Spectral nativeHeat076Qm
    nativeHeat076Variance_formula nativeHeat076Qm_formula ?_ ?_ ?_ ?_
    nativeHeat076BaseOk_Gen nativeHeat076RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap077Old]
  · norm_num [nativeHeat076Variance]
  · norm_num [nativeHeat076Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat076Qm]

theorem nativeHeat077BaseOk_Gen : nativeHeatGenBaseOk nativeHeat077Qm = true := by
  decide +kernel

theorem nativeHeat077RootOk_Gen : nativeHeatGenRootOk nativeHeat077Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_77_Gen : NativeHeatGenNum 77 := by
  refine nativeHeatGenNum_of_data 77 (by norm_num) nativeGap078Old ?_
    nativeHeat077Variance nativeHeat077Spectral nativeHeat077Qm
    nativeHeat077Variance_formula nativeHeat077Qm_formula ?_ ?_ ?_ ?_
    nativeHeat077BaseOk_Gen nativeHeat077RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap078Old]
  · norm_num [nativeHeat077Variance]
  · norm_num [nativeHeat077Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat077Qm]

theorem nativeHeat078BaseOk_Gen : nativeHeatGenBaseOk nativeHeat078Qm = true := by
  decide +kernel

theorem nativeHeat078RootOk_Gen : nativeHeatGenRootOk nativeHeat078Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_78_Gen : NativeHeatGenNum 78 := by
  refine nativeHeatGenNum_of_data 78 (by norm_num) nativeGap079Old ?_
    nativeHeat078Variance nativeHeat078Spectral nativeHeat078Qm
    nativeHeat078Variance_formula nativeHeat078Qm_formula ?_ ?_ ?_ ?_
    nativeHeat078BaseOk_Gen nativeHeat078RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap079Old]
  · norm_num [nativeHeat078Variance]
  · norm_num [nativeHeat078Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat078Qm]

theorem nativeHeat079BaseOk_Gen : nativeHeatGenBaseOk nativeHeat079Qm = true := by
  decide +kernel

theorem nativeHeat079RootOk_Gen : nativeHeatGenRootOk nativeHeat079Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_79_Gen : NativeHeatGenNum 79 := by
  refine nativeHeatGenNum_of_data 79 (by norm_num) nativeGap080Old ?_
    nativeHeat079Variance nativeHeat079Spectral nativeHeat079Qm
    nativeHeat079Variance_formula nativeHeat079Qm_formula ?_ ?_ ?_ ?_
    nativeHeat079BaseOk_Gen nativeHeat079RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap080Old]
  · norm_num [nativeHeat079Variance]
  · norm_num [nativeHeat079Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat079Qm]

theorem nativeHeat080BaseOk_Gen : nativeHeatGenBaseOk nativeHeat080Qm = true := by
  decide +kernel

theorem nativeHeat080RootOk_Gen : nativeHeatGenRootOk nativeHeat080Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_80_Gen : NativeHeatGenNum 80 := by
  refine nativeHeatGenNum_of_data 80 (by norm_num) nativeGap081Old ?_
    nativeHeat080Variance nativeHeat080Spectral nativeHeat080Qm
    nativeHeat080Variance_formula nativeHeat080Qm_formula ?_ ?_ ?_ ?_
    nativeHeat080BaseOk_Gen nativeHeat080RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap081Old]
  · norm_num [nativeHeat080Variance]
  · norm_num [nativeHeat080Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat080Qm]

theorem nativeHeat081BaseOk_Gen : nativeHeatGenBaseOk nativeHeat081Qm = true := by
  decide +kernel

theorem nativeHeat081RootOk_Gen : nativeHeatGenRootOk nativeHeat081Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_81_Gen : NativeHeatGenNum 81 := by
  refine nativeHeatGenNum_of_data 81 (by norm_num) nativeGap082Old ?_
    nativeHeat081Variance nativeHeat081Spectral nativeHeat081Qm
    nativeHeat081Variance_formula nativeHeat081Qm_formula ?_ ?_ ?_ ?_
    nativeHeat081BaseOk_Gen nativeHeat081RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap082Old]
  · norm_num [nativeHeat081Variance]
  · norm_num [nativeHeat081Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat081Qm]

theorem nativeHeat082BaseOk_Gen : nativeHeatGenBaseOk nativeHeat082Qm = true := by
  decide +kernel

theorem nativeHeat082RootOk_Gen : nativeHeatGenRootOk nativeHeat082Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_82_Gen : NativeHeatGenNum 82 := by
  refine nativeHeatGenNum_of_data 82 (by norm_num) nativeGap083Old ?_
    nativeHeat082Variance nativeHeat082Spectral nativeHeat082Qm
    nativeHeat082Variance_formula nativeHeat082Qm_formula ?_ ?_ ?_ ?_
    nativeHeat082BaseOk_Gen nativeHeat082RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap083Old]
  · norm_num [nativeHeat082Variance]
  · norm_num [nativeHeat082Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat082Qm]

theorem nativeHeat083BaseOk_Gen : nativeHeatGenBaseOk nativeHeat083Qm = true := by
  decide +kernel

theorem nativeHeat083RootOk_Gen : nativeHeatGenRootOk nativeHeat083Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_83_Gen : NativeHeatGenNum 83 := by
  refine nativeHeatGenNum_of_data 83 (by norm_num) nativeGap084Old ?_
    nativeHeat083Variance nativeHeat083Spectral nativeHeat083Qm
    nativeHeat083Variance_formula nativeHeat083Qm_formula ?_ ?_ ?_ ?_
    nativeHeat083BaseOk_Gen nativeHeat083RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap084Old]
  · norm_num [nativeHeat083Variance]
  · norm_num [nativeHeat083Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat083Qm]

theorem nativeHeat084BaseOk_Gen : nativeHeatGenBaseOk nativeHeat084Qm = true := by
  decide +kernel

theorem nativeHeat084RootOk_Gen : nativeHeatGenRootOk nativeHeat084Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_84_Gen : NativeHeatGenNum 84 := by
  refine nativeHeatGenNum_of_data 84 (by norm_num) nativeGap085Old ?_
    nativeHeat084Variance nativeHeat084Spectral nativeHeat084Qm
    nativeHeat084Variance_formula nativeHeat084Qm_formula ?_ ?_ ?_ ?_
    nativeHeat084BaseOk_Gen nativeHeat084RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap085Old]
  · norm_num [nativeHeat084Variance]
  · norm_num [nativeHeat084Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat084Qm]

theorem nativeHeatGenNum_range4_Gen (ns : ℕ) (h1 : 66 ≤ ns) (h2 : ns < 85) :
    NativeHeatGenNum ns := by
  by_cases hh66 : ns = 66
  · subst hh66; exact nativeHeatGenNum_66_Gen
  by_cases hh67 : ns = 67
  · subst hh67; exact nativeHeatGenNum_67_Gen
  by_cases hh68 : ns = 68
  · subst hh68; exact nativeHeatGenNum_68_Gen
  by_cases hh69 : ns = 69
  · subst hh69; exact nativeHeatGenNum_69_Gen
  by_cases hh70 : ns = 70
  · subst hh70; exact nativeHeatGenNum_70_Gen
  by_cases hh71 : ns = 71
  · subst hh71; exact nativeHeatGenNum_71_Gen
  by_cases hh72 : ns = 72
  · subst hh72; exact nativeHeatGenNum_72_Gen
  by_cases hh73 : ns = 73
  · subst hh73; exact nativeHeatGenNum_73_Gen
  by_cases hh74 : ns = 74
  · subst hh74; exact nativeHeatGenNum_74_Gen
  by_cases hh75 : ns = 75
  · subst hh75; exact nativeHeatGenNum_75_Gen
  by_cases hh76 : ns = 76
  · subst hh76; exact nativeHeatGenNum_76_Gen
  by_cases hh77 : ns = 77
  · subst hh77; exact nativeHeatGenNum_77_Gen
  by_cases hh78 : ns = 78
  · subst hh78; exact nativeHeatGenNum_78_Gen
  by_cases hh79 : ns = 79
  · subst hh79; exact nativeHeatGenNum_79_Gen
  by_cases hh80 : ns = 80
  · subst hh80; exact nativeHeatGenNum_80_Gen
  by_cases hh81 : ns = 81
  · subst hh81; exact nativeHeatGenNum_81_Gen
  by_cases hh82 : ns = 82
  · subst hh82; exact nativeHeatGenNum_82_Gen
  by_cases hh83 : ns = 83
  · subst hh83; exact nativeHeatGenNum_83_Gen
  have hh : ns = 84 := by omega
  subst hh; exact nativeHeatGenNum_84_Gen

end ASDExplicitGamma.Native
