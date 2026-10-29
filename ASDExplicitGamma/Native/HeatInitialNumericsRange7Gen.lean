module

public import ASDExplicitGamma.Native.HeatInitialNumericsDataGen
public import ASDExplicitGamma.Numerics.Native.Heat123Initial
public import ASDExplicitGamma.Numerics.Native.Heat124Initial
public import ASDExplicitGamma.Numerics.Native.Heat125Initial
public import ASDExplicitGamma.Numerics.Native.Heat126Initial
public import ASDExplicitGamma.Numerics.Native.Heat127Initial
public import ASDExplicitGamma.Numerics.Native.Heat128Initial
public import ASDExplicitGamma.Numerics.Native.Heat129Initial
public import ASDExplicitGamma.Numerics.Native.Heat130Initial
public import ASDExplicitGamma.Numerics.Native.Heat131Initial
public import ASDExplicitGamma.Numerics.Native.Heat132Initial
public import ASDExplicitGamma.Numerics.Native.Heat133Initial
public import ASDExplicitGamma.Numerics.Native.Heat134Initial
public import ASDExplicitGamma.Numerics.Native.Heat135Initial
public import ASDExplicitGamma.Numerics.Native.Heat136Initial
public import ASDExplicitGamma.Numerics.Native.Heat137Initial
public import ASDExplicitGamma.Numerics.Native.Heat138Initial
public import ASDExplicitGamma.Numerics.Native.Heat139Initial
public import ASDExplicitGamma.Numerics.Native.Heat140Initial
public import ASDExplicitGamma.Numerics.Native.Heat141Initial

/-! Numeric certificates of the `ns`-shell refined initial moment for `123 ≤ ns < 142`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

theorem nativeHeat123BaseOk_Gen : nativeHeatGenBaseOk nativeHeat123Qm = true := by
  decide +kernel

theorem nativeHeat123RootOk_Gen : nativeHeatGenRootOk nativeHeat123Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_123_Gen : NativeHeatGenNum 123 := by
  refine nativeHeatGenNum_of_data 123 (by norm_num) nativeGap124Old ?_
    nativeHeat123Variance nativeHeat123Spectral nativeHeat123Qm
    nativeHeat123Variance_formula nativeHeat123Qm_formula ?_ ?_ ?_ ?_
    nativeHeat123BaseOk_Gen nativeHeat123RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap124Old]
  · norm_num [nativeHeat123Variance]
  · norm_num [nativeHeat123Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat123Qm]

theorem nativeHeat124BaseOk_Gen : nativeHeatGenBaseOk nativeHeat124Qm = true := by
  decide +kernel

theorem nativeHeat124RootOk_Gen : nativeHeatGenRootOk nativeHeat124Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_124_Gen : NativeHeatGenNum 124 := by
  refine nativeHeatGenNum_of_data 124 (by norm_num) nativeGap125Old ?_
    nativeHeat124Variance nativeHeat124Spectral nativeHeat124Qm
    nativeHeat124Variance_formula nativeHeat124Qm_formula ?_ ?_ ?_ ?_
    nativeHeat124BaseOk_Gen nativeHeat124RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap125Old]
  · norm_num [nativeHeat124Variance]
  · norm_num [nativeHeat124Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat124Qm]

theorem nativeHeat125BaseOk_Gen : nativeHeatGenBaseOk nativeHeat125Qm = true := by
  decide +kernel

theorem nativeHeat125RootOk_Gen : nativeHeatGenRootOk nativeHeat125Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_125_Gen : NativeHeatGenNum 125 := by
  refine nativeHeatGenNum_of_data 125 (by norm_num) nativeGap126Old ?_
    nativeHeat125Variance nativeHeat125Spectral nativeHeat125Qm
    nativeHeat125Variance_formula nativeHeat125Qm_formula ?_ ?_ ?_ ?_
    nativeHeat125BaseOk_Gen nativeHeat125RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap126Old]
  · norm_num [nativeHeat125Variance]
  · norm_num [nativeHeat125Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat125Qm]

theorem nativeHeat126BaseOk_Gen : nativeHeatGenBaseOk nativeHeat126Qm = true := by
  decide +kernel

theorem nativeHeat126RootOk_Gen : nativeHeatGenRootOk nativeHeat126Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_126_Gen : NativeHeatGenNum 126 := by
  refine nativeHeatGenNum_of_data 126 (by norm_num) nativeGap127Old ?_
    nativeHeat126Variance nativeHeat126Spectral nativeHeat126Qm
    nativeHeat126Variance_formula nativeHeat126Qm_formula ?_ ?_ ?_ ?_
    nativeHeat126BaseOk_Gen nativeHeat126RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap127Old]
  · norm_num [nativeHeat126Variance]
  · norm_num [nativeHeat126Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat126Qm]

theorem nativeHeat127BaseOk_Gen : nativeHeatGenBaseOk nativeHeat127Qm = true := by
  decide +kernel

theorem nativeHeat127RootOk_Gen : nativeHeatGenRootOk nativeHeat127Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_127_Gen : NativeHeatGenNum 127 := by
  refine nativeHeatGenNum_of_data 127 (by norm_num) nativeGap128Old ?_
    nativeHeat127Variance nativeHeat127Spectral nativeHeat127Qm
    nativeHeat127Variance_formula nativeHeat127Qm_formula ?_ ?_ ?_ ?_
    nativeHeat127BaseOk_Gen nativeHeat127RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap128Old]
  · norm_num [nativeHeat127Variance]
  · norm_num [nativeHeat127Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat127Qm]

theorem nativeHeat128BaseOk_Gen : nativeHeatGenBaseOk nativeHeat128Qm = true := by
  decide +kernel

theorem nativeHeat128RootOk_Gen : nativeHeatGenRootOk nativeHeat128Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_128_Gen : NativeHeatGenNum 128 := by
  refine nativeHeatGenNum_of_data 128 (by norm_num) nativeGap129Old ?_
    nativeHeat128Variance nativeHeat128Spectral nativeHeat128Qm
    nativeHeat128Variance_formula nativeHeat128Qm_formula ?_ ?_ ?_ ?_
    nativeHeat128BaseOk_Gen nativeHeat128RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap129Old]
  · norm_num [nativeHeat128Variance]
  · norm_num [nativeHeat128Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat128Qm]

theorem nativeHeat129BaseOk_Gen : nativeHeatGenBaseOk nativeHeat129Qm = true := by
  decide +kernel

theorem nativeHeat129RootOk_Gen : nativeHeatGenRootOk nativeHeat129Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_129_Gen : NativeHeatGenNum 129 := by
  refine nativeHeatGenNum_of_data 129 (by norm_num) nativeGap130Old ?_
    nativeHeat129Variance nativeHeat129Spectral nativeHeat129Qm
    nativeHeat129Variance_formula nativeHeat129Qm_formula ?_ ?_ ?_ ?_
    nativeHeat129BaseOk_Gen nativeHeat129RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap130Old]
  · norm_num [nativeHeat129Variance]
  · norm_num [nativeHeat129Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat129Qm]

theorem nativeHeat130BaseOk_Gen : nativeHeatGenBaseOk nativeHeat130Qm = true := by
  decide +kernel

theorem nativeHeat130RootOk_Gen : nativeHeatGenRootOk nativeHeat130Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_130_Gen : NativeHeatGenNum 130 := by
  refine nativeHeatGenNum_of_data 130 (by norm_num) nativeGap131Old ?_
    nativeHeat130Variance nativeHeat130Spectral nativeHeat130Qm
    nativeHeat130Variance_formula nativeHeat130Qm_formula ?_ ?_ ?_ ?_
    nativeHeat130BaseOk_Gen nativeHeat130RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap131Old]
  · norm_num [nativeHeat130Variance]
  · norm_num [nativeHeat130Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat130Qm]

theorem nativeHeat131BaseOk_Gen : nativeHeatGenBaseOk nativeHeat131Qm = true := by
  decide +kernel

theorem nativeHeat131RootOk_Gen : nativeHeatGenRootOk nativeHeat131Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_131_Gen : NativeHeatGenNum 131 := by
  refine nativeHeatGenNum_of_data 131 (by norm_num) nativeGap132Old ?_
    nativeHeat131Variance nativeHeat131Spectral nativeHeat131Qm
    nativeHeat131Variance_formula nativeHeat131Qm_formula ?_ ?_ ?_ ?_
    nativeHeat131BaseOk_Gen nativeHeat131RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap132Old]
  · norm_num [nativeHeat131Variance]
  · norm_num [nativeHeat131Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat131Qm]

theorem nativeHeat132BaseOk_Gen : nativeHeatGenBaseOk nativeHeat132Qm = true := by
  decide +kernel

theorem nativeHeat132RootOk_Gen : nativeHeatGenRootOk nativeHeat132Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_132_Gen : NativeHeatGenNum 132 := by
  refine nativeHeatGenNum_of_data 132 (by norm_num) nativeGap133Old ?_
    nativeHeat132Variance nativeHeat132Spectral nativeHeat132Qm
    nativeHeat132Variance_formula nativeHeat132Qm_formula ?_ ?_ ?_ ?_
    nativeHeat132BaseOk_Gen nativeHeat132RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap133Old]
  · norm_num [nativeHeat132Variance]
  · norm_num [nativeHeat132Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat132Qm]

theorem nativeHeat133BaseOk_Gen : nativeHeatGenBaseOk nativeHeat133Qm = true := by
  decide +kernel

theorem nativeHeat133RootOk_Gen : nativeHeatGenRootOk nativeHeat133Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_133_Gen : NativeHeatGenNum 133 := by
  refine nativeHeatGenNum_of_data 133 (by norm_num) nativeGap134Old ?_
    nativeHeat133Variance nativeHeat133Spectral nativeHeat133Qm
    nativeHeat133Variance_formula nativeHeat133Qm_formula ?_ ?_ ?_ ?_
    nativeHeat133BaseOk_Gen nativeHeat133RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap134Old]
  · norm_num [nativeHeat133Variance]
  · norm_num [nativeHeat133Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat133Qm]

theorem nativeHeat134BaseOk_Gen : nativeHeatGenBaseOk nativeHeat134Qm = true := by
  decide +kernel

theorem nativeHeat134RootOk_Gen : nativeHeatGenRootOk nativeHeat134Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_134_Gen : NativeHeatGenNum 134 := by
  refine nativeHeatGenNum_of_data 134 (by norm_num) nativeGap135Old ?_
    nativeHeat134Variance nativeHeat134Spectral nativeHeat134Qm
    nativeHeat134Variance_formula nativeHeat134Qm_formula ?_ ?_ ?_ ?_
    nativeHeat134BaseOk_Gen nativeHeat134RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap135Old]
  · norm_num [nativeHeat134Variance]
  · norm_num [nativeHeat134Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat134Qm]

theorem nativeHeat135BaseOk_Gen : nativeHeatGenBaseOk nativeHeat135Qm = true := by
  decide +kernel

theorem nativeHeat135RootOk_Gen : nativeHeatGenRootOk nativeHeat135Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_135_Gen : NativeHeatGenNum 135 := by
  refine nativeHeatGenNum_of_data 135 (by norm_num) nativeGap136Old ?_
    nativeHeat135Variance nativeHeat135Spectral nativeHeat135Qm
    nativeHeat135Variance_formula nativeHeat135Qm_formula ?_ ?_ ?_ ?_
    nativeHeat135BaseOk_Gen nativeHeat135RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap136Old]
  · norm_num [nativeHeat135Variance]
  · norm_num [nativeHeat135Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat135Qm]

theorem nativeHeat136BaseOk_Gen : nativeHeatGenBaseOk nativeHeat136Qm = true := by
  decide +kernel

theorem nativeHeat136RootOk_Gen : nativeHeatGenRootOk nativeHeat136Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_136_Gen : NativeHeatGenNum 136 := by
  refine nativeHeatGenNum_of_data 136 (by norm_num) nativeGap137Old ?_
    nativeHeat136Variance nativeHeat136Spectral nativeHeat136Qm
    nativeHeat136Variance_formula nativeHeat136Qm_formula ?_ ?_ ?_ ?_
    nativeHeat136BaseOk_Gen nativeHeat136RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap137Old]
  · norm_num [nativeHeat136Variance]
  · norm_num [nativeHeat136Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat136Qm]

theorem nativeHeat137BaseOk_Gen : nativeHeatGenBaseOk nativeHeat137Qm = true := by
  decide +kernel

theorem nativeHeat137RootOk_Gen : nativeHeatGenRootOk nativeHeat137Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_137_Gen : NativeHeatGenNum 137 := by
  refine nativeHeatGenNum_of_data 137 (by norm_num) nativeGap138Old ?_
    nativeHeat137Variance nativeHeat137Spectral nativeHeat137Qm
    nativeHeat137Variance_formula nativeHeat137Qm_formula ?_ ?_ ?_ ?_
    nativeHeat137BaseOk_Gen nativeHeat137RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap138Old]
  · norm_num [nativeHeat137Variance]
  · norm_num [nativeHeat137Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat137Qm]

theorem nativeHeat138BaseOk_Gen : nativeHeatGenBaseOk nativeHeat138Qm = true := by
  decide +kernel

theorem nativeHeat138RootOk_Gen : nativeHeatGenRootOk nativeHeat138Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_138_Gen : NativeHeatGenNum 138 := by
  refine nativeHeatGenNum_of_data 138 (by norm_num) nativeGap139Old ?_
    nativeHeat138Variance nativeHeat138Spectral nativeHeat138Qm
    nativeHeat138Variance_formula nativeHeat138Qm_formula ?_ ?_ ?_ ?_
    nativeHeat138BaseOk_Gen nativeHeat138RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap139Old]
  · norm_num [nativeHeat138Variance]
  · norm_num [nativeHeat138Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat138Qm]

theorem nativeHeat139BaseOk_Gen : nativeHeatGenBaseOk nativeHeat139Qm = true := by
  decide +kernel

theorem nativeHeat139RootOk_Gen : nativeHeatGenRootOk nativeHeat139Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_139_Gen : NativeHeatGenNum 139 := by
  refine nativeHeatGenNum_of_data 139 (by norm_num) nativeGap140Old ?_
    nativeHeat139Variance nativeHeat139Spectral nativeHeat139Qm
    nativeHeat139Variance_formula nativeHeat139Qm_formula ?_ ?_ ?_ ?_
    nativeHeat139BaseOk_Gen nativeHeat139RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap140Old]
  · norm_num [nativeHeat139Variance]
  · norm_num [nativeHeat139Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat139Qm]

theorem nativeHeat140BaseOk_Gen : nativeHeatGenBaseOk nativeHeat140Qm = true := by
  decide +kernel

theorem nativeHeat140RootOk_Gen : nativeHeatGenRootOk nativeHeat140Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_140_Gen : NativeHeatGenNum 140 := by
  refine nativeHeatGenNum_of_data 140 (by norm_num) nativeGap141Old ?_
    nativeHeat140Variance nativeHeat140Spectral nativeHeat140Qm
    nativeHeat140Variance_formula nativeHeat140Qm_formula ?_ ?_ ?_ ?_
    nativeHeat140BaseOk_Gen nativeHeat140RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap141Old]
  · norm_num [nativeHeat140Variance]
  · norm_num [nativeHeat140Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat140Qm]

theorem nativeHeat141BaseOk_Gen : nativeHeatGenBaseOk nativeHeat141Qm = true := by
  decide +kernel

theorem nativeHeat141RootOk_Gen : nativeHeatGenRootOk nativeHeat141Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_141_Gen : NativeHeatGenNum 141 := by
  refine nativeHeatGenNum_of_data 141 (by norm_num) nativeGap142Old ?_
    nativeHeat141Variance nativeHeat141Spectral nativeHeat141Qm
    nativeHeat141Variance_formula nativeHeat141Qm_formula ?_ ?_ ?_ ?_
    nativeHeat141BaseOk_Gen nativeHeat141RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap142Old]
  · norm_num [nativeHeat141Variance]
  · norm_num [nativeHeat141Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat141Qm]

theorem nativeHeatGenNum_range7_Gen (ns : ℕ) (h1 : 123 ≤ ns) (h2 : ns < 142) :
    NativeHeatGenNum ns := by
  by_cases hh123 : ns = 123
  · subst hh123; exact nativeHeatGenNum_123_Gen
  by_cases hh124 : ns = 124
  · subst hh124; exact nativeHeatGenNum_124_Gen
  by_cases hh125 : ns = 125
  · subst hh125; exact nativeHeatGenNum_125_Gen
  by_cases hh126 : ns = 126
  · subst hh126; exact nativeHeatGenNum_126_Gen
  by_cases hh127 : ns = 127
  · subst hh127; exact nativeHeatGenNum_127_Gen
  by_cases hh128 : ns = 128
  · subst hh128; exact nativeHeatGenNum_128_Gen
  by_cases hh129 : ns = 129
  · subst hh129; exact nativeHeatGenNum_129_Gen
  by_cases hh130 : ns = 130
  · subst hh130; exact nativeHeatGenNum_130_Gen
  by_cases hh131 : ns = 131
  · subst hh131; exact nativeHeatGenNum_131_Gen
  by_cases hh132 : ns = 132
  · subst hh132; exact nativeHeatGenNum_132_Gen
  by_cases hh133 : ns = 133
  · subst hh133; exact nativeHeatGenNum_133_Gen
  by_cases hh134 : ns = 134
  · subst hh134; exact nativeHeatGenNum_134_Gen
  by_cases hh135 : ns = 135
  · subst hh135; exact nativeHeatGenNum_135_Gen
  by_cases hh136 : ns = 136
  · subst hh136; exact nativeHeatGenNum_136_Gen
  by_cases hh137 : ns = 137
  · subst hh137; exact nativeHeatGenNum_137_Gen
  by_cases hh138 : ns = 138
  · subst hh138; exact nativeHeatGenNum_138_Gen
  by_cases hh139 : ns = 139
  · subst hh139; exact nativeHeatGenNum_139_Gen
  by_cases hh140 : ns = 140
  · subst hh140; exact nativeHeatGenNum_140_Gen
  have hh : ns = 141 := by omega
  subst hh; exact nativeHeatGenNum_141_Gen

end ASDExplicitGamma.Native
