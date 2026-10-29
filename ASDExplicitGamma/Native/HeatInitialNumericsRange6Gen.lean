module

public import ASDExplicitGamma.Native.HeatInitialNumericsDataGen
public import ASDExplicitGamma.Numerics.Native.Heat104Initial
public import ASDExplicitGamma.Numerics.Native.Heat105Initial
public import ASDExplicitGamma.Numerics.Native.Heat106Initial
public import ASDExplicitGamma.Numerics.Native.Heat107Initial
public import ASDExplicitGamma.Numerics.Native.Heat108Initial
public import ASDExplicitGamma.Numerics.Native.Heat109Initial
public import ASDExplicitGamma.Numerics.Native.Heat110Initial
public import ASDExplicitGamma.Numerics.Native.Heat111Initial
public import ASDExplicitGamma.Numerics.Native.Heat112Initial
public import ASDExplicitGamma.Numerics.Native.Heat113Initial
public import ASDExplicitGamma.Numerics.Native.Heat114Initial
public import ASDExplicitGamma.Numerics.Native.Heat115Initial
public import ASDExplicitGamma.Numerics.Native.Heat116Initial
public import ASDExplicitGamma.Numerics.Native.Heat117Initial
public import ASDExplicitGamma.Numerics.Native.Heat118Initial
public import ASDExplicitGamma.Numerics.Native.Heat119Initial
public import ASDExplicitGamma.Numerics.Native.Heat120Initial
public import ASDExplicitGamma.Numerics.Native.Heat121Initial
public import ASDExplicitGamma.Numerics.Native.Heat122Initial

/-! Numeric certificates of the `ns`-shell refined initial moment for `104 ≤ ns < 123`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

theorem nativeHeat104BaseOk_Gen : nativeHeatGenBaseOk nativeHeat104Qm = true := by
  decide +kernel

theorem nativeHeat104RootOk_Gen : nativeHeatGenRootOk nativeHeat104Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_104_Gen : NativeHeatGenNum 104 := by
  refine nativeHeatGenNum_of_data 104 (by norm_num) nativeGap105Old ?_
    nativeHeat104Variance nativeHeat104Spectral nativeHeat104Qm
    nativeHeat104Variance_formula nativeHeat104Qm_formula ?_ ?_ ?_ ?_
    nativeHeat104BaseOk_Gen nativeHeat104RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap105Old]
  · norm_num [nativeHeat104Variance]
  · norm_num [nativeHeat104Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat104Qm]

theorem nativeHeat105BaseOk_Gen : nativeHeatGenBaseOk nativeHeat105Qm = true := by
  decide +kernel

theorem nativeHeat105RootOk_Gen : nativeHeatGenRootOk nativeHeat105Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_105_Gen : NativeHeatGenNum 105 := by
  refine nativeHeatGenNum_of_data 105 (by norm_num) nativeGap106Old ?_
    nativeHeat105Variance nativeHeat105Spectral nativeHeat105Qm
    nativeHeat105Variance_formula nativeHeat105Qm_formula ?_ ?_ ?_ ?_
    nativeHeat105BaseOk_Gen nativeHeat105RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap106Old]
  · norm_num [nativeHeat105Variance]
  · norm_num [nativeHeat105Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat105Qm]

theorem nativeHeat106BaseOk_Gen : nativeHeatGenBaseOk nativeHeat106Qm = true := by
  decide +kernel

theorem nativeHeat106RootOk_Gen : nativeHeatGenRootOk nativeHeat106Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_106_Gen : NativeHeatGenNum 106 := by
  refine nativeHeatGenNum_of_data 106 (by norm_num) nativeGap107Old ?_
    nativeHeat106Variance nativeHeat106Spectral nativeHeat106Qm
    nativeHeat106Variance_formula nativeHeat106Qm_formula ?_ ?_ ?_ ?_
    nativeHeat106BaseOk_Gen nativeHeat106RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap107Old]
  · norm_num [nativeHeat106Variance]
  · norm_num [nativeHeat106Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat106Qm]

theorem nativeHeat107BaseOk_Gen : nativeHeatGenBaseOk nativeHeat107Qm = true := by
  decide +kernel

theorem nativeHeat107RootOk_Gen : nativeHeatGenRootOk nativeHeat107Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_107_Gen : NativeHeatGenNum 107 := by
  refine nativeHeatGenNum_of_data 107 (by norm_num) nativeGap108Old ?_
    nativeHeat107Variance nativeHeat107Spectral nativeHeat107Qm
    nativeHeat107Variance_formula nativeHeat107Qm_formula ?_ ?_ ?_ ?_
    nativeHeat107BaseOk_Gen nativeHeat107RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap108Old]
  · norm_num [nativeHeat107Variance]
  · norm_num [nativeHeat107Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat107Qm]

theorem nativeHeat108BaseOk_Gen : nativeHeatGenBaseOk nativeHeat108Qm = true := by
  decide +kernel

theorem nativeHeat108RootOk_Gen : nativeHeatGenRootOk nativeHeat108Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_108_Gen : NativeHeatGenNum 108 := by
  refine nativeHeatGenNum_of_data 108 (by norm_num) nativeGap109Old ?_
    nativeHeat108Variance nativeHeat108Spectral nativeHeat108Qm
    nativeHeat108Variance_formula nativeHeat108Qm_formula ?_ ?_ ?_ ?_
    nativeHeat108BaseOk_Gen nativeHeat108RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap109Old]
  · norm_num [nativeHeat108Variance]
  · norm_num [nativeHeat108Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat108Qm]

theorem nativeHeat109BaseOk_Gen : nativeHeatGenBaseOk nativeHeat109Qm = true := by
  decide +kernel

theorem nativeHeat109RootOk_Gen : nativeHeatGenRootOk nativeHeat109Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_109_Gen : NativeHeatGenNum 109 := by
  refine nativeHeatGenNum_of_data 109 (by norm_num) nativeGap110Old ?_
    nativeHeat109Variance nativeHeat109Spectral nativeHeat109Qm
    nativeHeat109Variance_formula nativeHeat109Qm_formula ?_ ?_ ?_ ?_
    nativeHeat109BaseOk_Gen nativeHeat109RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap110Old]
  · norm_num [nativeHeat109Variance]
  · norm_num [nativeHeat109Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat109Qm]

theorem nativeHeat110BaseOk_Gen : nativeHeatGenBaseOk nativeHeat110Qm = true := by
  decide +kernel

theorem nativeHeat110RootOk_Gen : nativeHeatGenRootOk nativeHeat110Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_110_Gen : NativeHeatGenNum 110 := by
  refine nativeHeatGenNum_of_data 110 (by norm_num) nativeGap111Old ?_
    nativeHeat110Variance nativeHeat110Spectral nativeHeat110Qm
    nativeHeat110Variance_formula nativeHeat110Qm_formula ?_ ?_ ?_ ?_
    nativeHeat110BaseOk_Gen nativeHeat110RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap111Old]
  · norm_num [nativeHeat110Variance]
  · norm_num [nativeHeat110Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat110Qm]

theorem nativeHeat111BaseOk_Gen : nativeHeatGenBaseOk nativeHeat111Qm = true := by
  decide +kernel

theorem nativeHeat111RootOk_Gen : nativeHeatGenRootOk nativeHeat111Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_111_Gen : NativeHeatGenNum 111 := by
  refine nativeHeatGenNum_of_data 111 (by norm_num) nativeGap112Old ?_
    nativeHeat111Variance nativeHeat111Spectral nativeHeat111Qm
    nativeHeat111Variance_formula nativeHeat111Qm_formula ?_ ?_ ?_ ?_
    nativeHeat111BaseOk_Gen nativeHeat111RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap112Old]
  · norm_num [nativeHeat111Variance]
  · norm_num [nativeHeat111Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat111Qm]

theorem nativeHeat112BaseOk_Gen : nativeHeatGenBaseOk nativeHeat112Qm = true := by
  decide +kernel

theorem nativeHeat112RootOk_Gen : nativeHeatGenRootOk nativeHeat112Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_112_Gen : NativeHeatGenNum 112 := by
  refine nativeHeatGenNum_of_data 112 (by norm_num) nativeGap113Old ?_
    nativeHeat112Variance nativeHeat112Spectral nativeHeat112Qm
    nativeHeat112Variance_formula nativeHeat112Qm_formula ?_ ?_ ?_ ?_
    nativeHeat112BaseOk_Gen nativeHeat112RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap113Old]
  · norm_num [nativeHeat112Variance]
  · norm_num [nativeHeat112Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat112Qm]

theorem nativeHeat113BaseOk_Gen : nativeHeatGenBaseOk nativeHeat113Qm = true := by
  decide +kernel

theorem nativeHeat113RootOk_Gen : nativeHeatGenRootOk nativeHeat113Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_113_Gen : NativeHeatGenNum 113 := by
  refine nativeHeatGenNum_of_data 113 (by norm_num) nativeGap114Old ?_
    nativeHeat113Variance nativeHeat113Spectral nativeHeat113Qm
    nativeHeat113Variance_formula nativeHeat113Qm_formula ?_ ?_ ?_ ?_
    nativeHeat113BaseOk_Gen nativeHeat113RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap114Old]
  · norm_num [nativeHeat113Variance]
  · norm_num [nativeHeat113Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat113Qm]

theorem nativeHeat114BaseOk_Gen : nativeHeatGenBaseOk nativeHeat114Qm = true := by
  decide +kernel

theorem nativeHeat114RootOk_Gen : nativeHeatGenRootOk nativeHeat114Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_114_Gen : NativeHeatGenNum 114 := by
  refine nativeHeatGenNum_of_data 114 (by norm_num) nativeGap115Old ?_
    nativeHeat114Variance nativeHeat114Spectral nativeHeat114Qm
    nativeHeat114Variance_formula nativeHeat114Qm_formula ?_ ?_ ?_ ?_
    nativeHeat114BaseOk_Gen nativeHeat114RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap115Old]
  · norm_num [nativeHeat114Variance]
  · norm_num [nativeHeat114Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat114Qm]

theorem nativeHeat115BaseOk_Gen : nativeHeatGenBaseOk nativeHeat115Qm = true := by
  decide +kernel

theorem nativeHeat115RootOk_Gen : nativeHeatGenRootOk nativeHeat115Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_115_Gen : NativeHeatGenNum 115 := by
  refine nativeHeatGenNum_of_data 115 (by norm_num) nativeGap116Old ?_
    nativeHeat115Variance nativeHeat115Spectral nativeHeat115Qm
    nativeHeat115Variance_formula nativeHeat115Qm_formula ?_ ?_ ?_ ?_
    nativeHeat115BaseOk_Gen nativeHeat115RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap116Old]
  · norm_num [nativeHeat115Variance]
  · norm_num [nativeHeat115Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat115Qm]

theorem nativeHeat116BaseOk_Gen : nativeHeatGenBaseOk nativeHeat116Qm = true := by
  decide +kernel

theorem nativeHeat116RootOk_Gen : nativeHeatGenRootOk nativeHeat116Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_116_Gen : NativeHeatGenNum 116 := by
  refine nativeHeatGenNum_of_data 116 (by norm_num) nativeGap117Old ?_
    nativeHeat116Variance nativeHeat116Spectral nativeHeat116Qm
    nativeHeat116Variance_formula nativeHeat116Qm_formula ?_ ?_ ?_ ?_
    nativeHeat116BaseOk_Gen nativeHeat116RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap117Old]
  · norm_num [nativeHeat116Variance]
  · norm_num [nativeHeat116Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat116Qm]

theorem nativeHeat117BaseOk_Gen : nativeHeatGenBaseOk nativeHeat117Qm = true := by
  decide +kernel

theorem nativeHeat117RootOk_Gen : nativeHeatGenRootOk nativeHeat117Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_117_Gen : NativeHeatGenNum 117 := by
  refine nativeHeatGenNum_of_data 117 (by norm_num) nativeGap118Old ?_
    nativeHeat117Variance nativeHeat117Spectral nativeHeat117Qm
    nativeHeat117Variance_formula nativeHeat117Qm_formula ?_ ?_ ?_ ?_
    nativeHeat117BaseOk_Gen nativeHeat117RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap118Old]
  · norm_num [nativeHeat117Variance]
  · norm_num [nativeHeat117Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat117Qm]

theorem nativeHeat118BaseOk_Gen : nativeHeatGenBaseOk nativeHeat118Qm = true := by
  decide +kernel

theorem nativeHeat118RootOk_Gen : nativeHeatGenRootOk nativeHeat118Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_118_Gen : NativeHeatGenNum 118 := by
  refine nativeHeatGenNum_of_data 118 (by norm_num) nativeGap119Old ?_
    nativeHeat118Variance nativeHeat118Spectral nativeHeat118Qm
    nativeHeat118Variance_formula nativeHeat118Qm_formula ?_ ?_ ?_ ?_
    nativeHeat118BaseOk_Gen nativeHeat118RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap119Old]
  · norm_num [nativeHeat118Variance]
  · norm_num [nativeHeat118Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat118Qm]

theorem nativeHeat119BaseOk_Gen : nativeHeatGenBaseOk nativeHeat119Qm = true := by
  decide +kernel

theorem nativeHeat119RootOk_Gen : nativeHeatGenRootOk nativeHeat119Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_119_Gen : NativeHeatGenNum 119 := by
  refine nativeHeatGenNum_of_data 119 (by norm_num) nativeGap120Old ?_
    nativeHeat119Variance nativeHeat119Spectral nativeHeat119Qm
    nativeHeat119Variance_formula nativeHeat119Qm_formula ?_ ?_ ?_ ?_
    nativeHeat119BaseOk_Gen nativeHeat119RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap120Old]
  · norm_num [nativeHeat119Variance]
  · norm_num [nativeHeat119Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat119Qm]

theorem nativeHeat120BaseOk_Gen : nativeHeatGenBaseOk nativeHeat120Qm = true := by
  decide +kernel

theorem nativeHeat120RootOk_Gen : nativeHeatGenRootOk nativeHeat120Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_120_Gen : NativeHeatGenNum 120 := by
  refine nativeHeatGenNum_of_data 120 (by norm_num) nativeGap121Old ?_
    nativeHeat120Variance nativeHeat120Spectral nativeHeat120Qm
    nativeHeat120Variance_formula nativeHeat120Qm_formula ?_ ?_ ?_ ?_
    nativeHeat120BaseOk_Gen nativeHeat120RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap121Old]
  · norm_num [nativeHeat120Variance]
  · norm_num [nativeHeat120Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat120Qm]

theorem nativeHeat121BaseOk_Gen : nativeHeatGenBaseOk nativeHeat121Qm = true := by
  decide +kernel

theorem nativeHeat121RootOk_Gen : nativeHeatGenRootOk nativeHeat121Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_121_Gen : NativeHeatGenNum 121 := by
  refine nativeHeatGenNum_of_data 121 (by norm_num) nativeGap122Old ?_
    nativeHeat121Variance nativeHeat121Spectral nativeHeat121Qm
    nativeHeat121Variance_formula nativeHeat121Qm_formula ?_ ?_ ?_ ?_
    nativeHeat121BaseOk_Gen nativeHeat121RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap122Old]
  · norm_num [nativeHeat121Variance]
  · norm_num [nativeHeat121Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat121Qm]

theorem nativeHeat122BaseOk_Gen : nativeHeatGenBaseOk nativeHeat122Qm = true := by
  decide +kernel

theorem nativeHeat122RootOk_Gen : nativeHeatGenRootOk nativeHeat122Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_122_Gen : NativeHeatGenNum 122 := by
  refine nativeHeatGenNum_of_data 122 (by norm_num) nativeGap123Old ?_
    nativeHeat122Variance nativeHeat122Spectral nativeHeat122Qm
    nativeHeat122Variance_formula nativeHeat122Qm_formula ?_ ?_ ?_ ?_
    nativeHeat122BaseOk_Gen nativeHeat122RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap123Old]
  · norm_num [nativeHeat122Variance]
  · norm_num [nativeHeat122Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat122Qm]

theorem nativeHeatGenNum_range6_Gen (ns : ℕ) (h1 : 104 ≤ ns) (h2 : ns < 123) :
    NativeHeatGenNum ns := by
  by_cases hh104 : ns = 104
  · subst hh104; exact nativeHeatGenNum_104_Gen
  by_cases hh105 : ns = 105
  · subst hh105; exact nativeHeatGenNum_105_Gen
  by_cases hh106 : ns = 106
  · subst hh106; exact nativeHeatGenNum_106_Gen
  by_cases hh107 : ns = 107
  · subst hh107; exact nativeHeatGenNum_107_Gen
  by_cases hh108 : ns = 108
  · subst hh108; exact nativeHeatGenNum_108_Gen
  by_cases hh109 : ns = 109
  · subst hh109; exact nativeHeatGenNum_109_Gen
  by_cases hh110 : ns = 110
  · subst hh110; exact nativeHeatGenNum_110_Gen
  by_cases hh111 : ns = 111
  · subst hh111; exact nativeHeatGenNum_111_Gen
  by_cases hh112 : ns = 112
  · subst hh112; exact nativeHeatGenNum_112_Gen
  by_cases hh113 : ns = 113
  · subst hh113; exact nativeHeatGenNum_113_Gen
  by_cases hh114 : ns = 114
  · subst hh114; exact nativeHeatGenNum_114_Gen
  by_cases hh115 : ns = 115
  · subst hh115; exact nativeHeatGenNum_115_Gen
  by_cases hh116 : ns = 116
  · subst hh116; exact nativeHeatGenNum_116_Gen
  by_cases hh117 : ns = 117
  · subst hh117; exact nativeHeatGenNum_117_Gen
  by_cases hh118 : ns = 118
  · subst hh118; exact nativeHeatGenNum_118_Gen
  by_cases hh119 : ns = 119
  · subst hh119; exact nativeHeatGenNum_119_Gen
  by_cases hh120 : ns = 120
  · subst hh120; exact nativeHeatGenNum_120_Gen
  by_cases hh121 : ns = 121
  · subst hh121; exact nativeHeatGenNum_121_Gen
  have hh : ns = 122 := by omega
  subst hh; exact nativeHeatGenNum_122_Gen

end ASDExplicitGamma.Native
