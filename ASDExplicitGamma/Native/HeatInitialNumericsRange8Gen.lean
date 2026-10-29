module

public import ASDExplicitGamma.Native.HeatInitialNumericsDataGen
public import ASDExplicitGamma.Numerics.Native.Heat142Initial
public import ASDExplicitGamma.Numerics.Native.Heat143Initial
public import ASDExplicitGamma.Numerics.Native.Heat144Initial
public import ASDExplicitGamma.Numerics.Native.Heat145Initial
public import ASDExplicitGamma.Numerics.Native.Heat146Initial
public import ASDExplicitGamma.Numerics.Native.Heat147Initial
public import ASDExplicitGamma.Numerics.Native.Heat148Initial
public import ASDExplicitGamma.Numerics.Native.Heat149Initial
public import ASDExplicitGamma.Numerics.Native.Heat150Initial
public import ASDExplicitGamma.Numerics.Native.Heat151Initial
public import ASDExplicitGamma.Numerics.Native.Heat152Initial
public import ASDExplicitGamma.Numerics.Native.Heat153Initial
public import ASDExplicitGamma.Numerics.Native.Heat154Initial
public import ASDExplicitGamma.Numerics.Native.Heat155Initial
public import ASDExplicitGamma.Numerics.Native.Heat156Initial
public import ASDExplicitGamma.Numerics.Native.Heat157Initial
public import ASDExplicitGamma.Numerics.Native.Heat158Initial
public import ASDExplicitGamma.Numerics.Native.Heat159Initial
public import ASDExplicitGamma.Numerics.Native.Heat160Initial

/-! Numeric certificates of the `ns`-shell refined initial moment for `142 ≤ ns < 161`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

theorem nativeHeat142BaseOk_Gen : nativeHeatGenBaseOk nativeHeat142Qm = true := by
  decide +kernel

theorem nativeHeat142RootOk_Gen : nativeHeatGenRootOk nativeHeat142Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_142_Gen : NativeHeatGenNum 142 := by
  refine nativeHeatGenNum_of_data 142 (by norm_num) nativeGap143Old ?_
    nativeHeat142Variance nativeHeat142Spectral nativeHeat142Qm
    nativeHeat142Variance_formula nativeHeat142Qm_formula ?_ ?_ ?_ ?_
    nativeHeat142BaseOk_Gen nativeHeat142RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap143Old]
  · norm_num [nativeHeat142Variance]
  · norm_num [nativeHeat142Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat142Qm]

theorem nativeHeat143BaseOk_Gen : nativeHeatGenBaseOk nativeHeat143Qm = true := by
  decide +kernel

theorem nativeHeat143RootOk_Gen : nativeHeatGenRootOk nativeHeat143Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_143_Gen : NativeHeatGenNum 143 := by
  refine nativeHeatGenNum_of_data 143 (by norm_num) nativeGap144Old ?_
    nativeHeat143Variance nativeHeat143Spectral nativeHeat143Qm
    nativeHeat143Variance_formula nativeHeat143Qm_formula ?_ ?_ ?_ ?_
    nativeHeat143BaseOk_Gen nativeHeat143RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap144Old]
  · norm_num [nativeHeat143Variance]
  · norm_num [nativeHeat143Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat143Qm]

theorem nativeHeat144BaseOk_Gen : nativeHeatGenBaseOk nativeHeat144Qm = true := by
  decide +kernel

theorem nativeHeat144RootOk_Gen : nativeHeatGenRootOk nativeHeat144Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_144_Gen : NativeHeatGenNum 144 := by
  refine nativeHeatGenNum_of_data 144 (by norm_num) nativeGap145Old ?_
    nativeHeat144Variance nativeHeat144Spectral nativeHeat144Qm
    nativeHeat144Variance_formula nativeHeat144Qm_formula ?_ ?_ ?_ ?_
    nativeHeat144BaseOk_Gen nativeHeat144RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap145Old]
  · norm_num [nativeHeat144Variance]
  · norm_num [nativeHeat144Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat144Qm]

theorem nativeHeat145BaseOk_Gen : nativeHeatGenBaseOk nativeHeat145Qm = true := by
  decide +kernel

theorem nativeHeat145RootOk_Gen : nativeHeatGenRootOk nativeHeat145Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_145_Gen : NativeHeatGenNum 145 := by
  refine nativeHeatGenNum_of_data 145 (by norm_num) nativeGap146Old ?_
    nativeHeat145Variance nativeHeat145Spectral nativeHeat145Qm
    nativeHeat145Variance_formula nativeHeat145Qm_formula ?_ ?_ ?_ ?_
    nativeHeat145BaseOk_Gen nativeHeat145RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap146Old]
  · norm_num [nativeHeat145Variance]
  · norm_num [nativeHeat145Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat145Qm]

theorem nativeHeat146BaseOk_Gen : nativeHeatGenBaseOk nativeHeat146Qm = true := by
  decide +kernel

theorem nativeHeat146RootOk_Gen : nativeHeatGenRootOk nativeHeat146Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_146_Gen : NativeHeatGenNum 146 := by
  refine nativeHeatGenNum_of_data 146 (by norm_num) nativeGap147Old ?_
    nativeHeat146Variance nativeHeat146Spectral nativeHeat146Qm
    nativeHeat146Variance_formula nativeHeat146Qm_formula ?_ ?_ ?_ ?_
    nativeHeat146BaseOk_Gen nativeHeat146RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap147Old]
  · norm_num [nativeHeat146Variance]
  · norm_num [nativeHeat146Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat146Qm]

theorem nativeHeat147BaseOk_Gen : nativeHeatGenBaseOk nativeHeat147Qm = true := by
  decide +kernel

theorem nativeHeat147RootOk_Gen : nativeHeatGenRootOk nativeHeat147Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_147_Gen : NativeHeatGenNum 147 := by
  refine nativeHeatGenNum_of_data 147 (by norm_num) nativeGap148Old ?_
    nativeHeat147Variance nativeHeat147Spectral nativeHeat147Qm
    nativeHeat147Variance_formula nativeHeat147Qm_formula ?_ ?_ ?_ ?_
    nativeHeat147BaseOk_Gen nativeHeat147RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap148Old]
  · norm_num [nativeHeat147Variance]
  · norm_num [nativeHeat147Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat147Qm]

theorem nativeHeat148BaseOk_Gen : nativeHeatGenBaseOk nativeHeat148Qm = true := by
  decide +kernel

theorem nativeHeat148RootOk_Gen : nativeHeatGenRootOk nativeHeat148Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_148_Gen : NativeHeatGenNum 148 := by
  refine nativeHeatGenNum_of_data 148 (by norm_num) nativeGap149Old ?_
    nativeHeat148Variance nativeHeat148Spectral nativeHeat148Qm
    nativeHeat148Variance_formula nativeHeat148Qm_formula ?_ ?_ ?_ ?_
    nativeHeat148BaseOk_Gen nativeHeat148RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap149Old]
  · norm_num [nativeHeat148Variance]
  · norm_num [nativeHeat148Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat148Qm]

theorem nativeHeat149BaseOk_Gen : nativeHeatGenBaseOk nativeHeat149Qm = true := by
  decide +kernel

theorem nativeHeat149RootOk_Gen : nativeHeatGenRootOk nativeHeat149Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_149_Gen : NativeHeatGenNum 149 := by
  refine nativeHeatGenNum_of_data 149 (by norm_num) nativeGap150Old ?_
    nativeHeat149Variance nativeHeat149Spectral nativeHeat149Qm
    nativeHeat149Variance_formula nativeHeat149Qm_formula ?_ ?_ ?_ ?_
    nativeHeat149BaseOk_Gen nativeHeat149RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap150Old]
  · norm_num [nativeHeat149Variance]
  · norm_num [nativeHeat149Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat149Qm]

theorem nativeHeat150BaseOk_Gen : nativeHeatGenBaseOk nativeHeat150Qm = true := by
  decide +kernel

theorem nativeHeat150RootOk_Gen : nativeHeatGenRootOk nativeHeat150Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_150_Gen : NativeHeatGenNum 150 := by
  refine nativeHeatGenNum_of_data 150 (by norm_num) nativeGap151Old ?_
    nativeHeat150Variance nativeHeat150Spectral nativeHeat150Qm
    nativeHeat150Variance_formula nativeHeat150Qm_formula ?_ ?_ ?_ ?_
    nativeHeat150BaseOk_Gen nativeHeat150RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap151Old]
  · norm_num [nativeHeat150Variance]
  · norm_num [nativeHeat150Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat150Qm]

theorem nativeHeat151BaseOk_Gen : nativeHeatGenBaseOk nativeHeat151Qm = true := by
  decide +kernel

theorem nativeHeat151RootOk_Gen : nativeHeatGenRootOk nativeHeat151Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_151_Gen : NativeHeatGenNum 151 := by
  refine nativeHeatGenNum_of_data 151 (by norm_num) nativeGap152Old ?_
    nativeHeat151Variance nativeHeat151Spectral nativeHeat151Qm
    nativeHeat151Variance_formula nativeHeat151Qm_formula ?_ ?_ ?_ ?_
    nativeHeat151BaseOk_Gen nativeHeat151RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap152Old]
  · norm_num [nativeHeat151Variance]
  · norm_num [nativeHeat151Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat151Qm]

theorem nativeHeat152BaseOk_Gen : nativeHeatGenBaseOk nativeHeat152Qm = true := by
  decide +kernel

theorem nativeHeat152RootOk_Gen : nativeHeatGenRootOk nativeHeat152Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_152_Gen : NativeHeatGenNum 152 := by
  refine nativeHeatGenNum_of_data 152 (by norm_num) nativeGap153Old ?_
    nativeHeat152Variance nativeHeat152Spectral nativeHeat152Qm
    nativeHeat152Variance_formula nativeHeat152Qm_formula ?_ ?_ ?_ ?_
    nativeHeat152BaseOk_Gen nativeHeat152RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap153Old]
  · norm_num [nativeHeat152Variance]
  · norm_num [nativeHeat152Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat152Qm]

theorem nativeHeat153BaseOk_Gen : nativeHeatGenBaseOk nativeHeat153Qm = true := by
  decide +kernel

theorem nativeHeat153RootOk_Gen : nativeHeatGenRootOk nativeHeat153Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_153_Gen : NativeHeatGenNum 153 := by
  refine nativeHeatGenNum_of_data 153 (by norm_num) nativeGap154Old ?_
    nativeHeat153Variance nativeHeat153Spectral nativeHeat153Qm
    nativeHeat153Variance_formula nativeHeat153Qm_formula ?_ ?_ ?_ ?_
    nativeHeat153BaseOk_Gen nativeHeat153RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap154Old]
  · norm_num [nativeHeat153Variance]
  · norm_num [nativeHeat153Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat153Qm]

theorem nativeHeat154BaseOk_Gen : nativeHeatGenBaseOk nativeHeat154Qm = true := by
  decide +kernel

theorem nativeHeat154RootOk_Gen : nativeHeatGenRootOk nativeHeat154Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_154_Gen : NativeHeatGenNum 154 := by
  refine nativeHeatGenNum_of_data 154 (by norm_num) nativeGap155Old ?_
    nativeHeat154Variance nativeHeat154Spectral nativeHeat154Qm
    nativeHeat154Variance_formula nativeHeat154Qm_formula ?_ ?_ ?_ ?_
    nativeHeat154BaseOk_Gen nativeHeat154RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap155Old]
  · norm_num [nativeHeat154Variance]
  · norm_num [nativeHeat154Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat154Qm]

theorem nativeHeat155BaseOk_Gen : nativeHeatGenBaseOk nativeHeat155Qm = true := by
  decide +kernel

theorem nativeHeat155RootOk_Gen : nativeHeatGenRootOk nativeHeat155Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_155_Gen : NativeHeatGenNum 155 := by
  refine nativeHeatGenNum_of_data 155 (by norm_num) nativeGap156Old ?_
    nativeHeat155Variance nativeHeat155Spectral nativeHeat155Qm
    nativeHeat155Variance_formula nativeHeat155Qm_formula ?_ ?_ ?_ ?_
    nativeHeat155BaseOk_Gen nativeHeat155RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap156Old]
  · norm_num [nativeHeat155Variance]
  · norm_num [nativeHeat155Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat155Qm]

theorem nativeHeat156BaseOk_Gen : nativeHeatGenBaseOk nativeHeat156Qm = true := by
  decide +kernel

theorem nativeHeat156RootOk_Gen : nativeHeatGenRootOk nativeHeat156Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_156_Gen : NativeHeatGenNum 156 := by
  refine nativeHeatGenNum_of_data 156 (by norm_num) nativeGap157Old ?_
    nativeHeat156Variance nativeHeat156Spectral nativeHeat156Qm
    nativeHeat156Variance_formula nativeHeat156Qm_formula ?_ ?_ ?_ ?_
    nativeHeat156BaseOk_Gen nativeHeat156RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap157Old]
  · norm_num [nativeHeat156Variance]
  · norm_num [nativeHeat156Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat156Qm]

theorem nativeHeat157BaseOk_Gen : nativeHeatGenBaseOk nativeHeat157Qm = true := by
  decide +kernel

theorem nativeHeat157RootOk_Gen : nativeHeatGenRootOk nativeHeat157Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_157_Gen : NativeHeatGenNum 157 := by
  refine nativeHeatGenNum_of_data 157 (by norm_num) nativeGap158Old ?_
    nativeHeat157Variance nativeHeat157Spectral nativeHeat157Qm
    nativeHeat157Variance_formula nativeHeat157Qm_formula ?_ ?_ ?_ ?_
    nativeHeat157BaseOk_Gen nativeHeat157RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap158Old]
  · norm_num [nativeHeat157Variance]
  · norm_num [nativeHeat157Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat157Qm]

theorem nativeHeat158BaseOk_Gen : nativeHeatGenBaseOk nativeHeat158Qm = true := by
  decide +kernel

theorem nativeHeat158RootOk_Gen : nativeHeatGenRootOk nativeHeat158Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_158_Gen : NativeHeatGenNum 158 := by
  refine nativeHeatGenNum_of_data 158 (by norm_num) nativeGap159Old ?_
    nativeHeat158Variance nativeHeat158Spectral nativeHeat158Qm
    nativeHeat158Variance_formula nativeHeat158Qm_formula ?_ ?_ ?_ ?_
    nativeHeat158BaseOk_Gen nativeHeat158RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap159Old]
  · norm_num [nativeHeat158Variance]
  · norm_num [nativeHeat158Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat158Qm]

theorem nativeHeat159BaseOk_Gen : nativeHeatGenBaseOk nativeHeat159Qm = true := by
  decide +kernel

theorem nativeHeat159RootOk_Gen : nativeHeatGenRootOk nativeHeat159Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_159_Gen : NativeHeatGenNum 159 := by
  refine nativeHeatGenNum_of_data 159 (by norm_num) nativeGap160Old ?_
    nativeHeat159Variance nativeHeat159Spectral nativeHeat159Qm
    nativeHeat159Variance_formula nativeHeat159Qm_formula ?_ ?_ ?_ ?_
    nativeHeat159BaseOk_Gen nativeHeat159RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap160Old]
  · norm_num [nativeHeat159Variance]
  · norm_num [nativeHeat159Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat159Qm]

theorem nativeHeat160BaseOk_Gen : nativeHeatGenBaseOk nativeHeat160Qm = true := by
  decide +kernel

theorem nativeHeat160RootOk_Gen : nativeHeatGenRootOk nativeHeat160Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_160_Gen : NativeHeatGenNum 160 := by
  refine nativeHeatGenNum_of_data 160 (by norm_num) nativeGap161Old ?_
    nativeHeat160Variance nativeHeat160Spectral nativeHeat160Qm
    nativeHeat160Variance_formula nativeHeat160Qm_formula ?_ ?_ ?_ ?_
    nativeHeat160BaseOk_Gen nativeHeat160RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap161Old]
  · norm_num [nativeHeat160Variance]
  · norm_num [nativeHeat160Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat160Qm]

theorem nativeHeatGenNum_range8_Gen (ns : ℕ) (h1 : 142 ≤ ns) (h2 : ns < 161) :
    NativeHeatGenNum ns := by
  by_cases hh142 : ns = 142
  · subst hh142; exact nativeHeatGenNum_142_Gen
  by_cases hh143 : ns = 143
  · subst hh143; exact nativeHeatGenNum_143_Gen
  by_cases hh144 : ns = 144
  · subst hh144; exact nativeHeatGenNum_144_Gen
  by_cases hh145 : ns = 145
  · subst hh145; exact nativeHeatGenNum_145_Gen
  by_cases hh146 : ns = 146
  · subst hh146; exact nativeHeatGenNum_146_Gen
  by_cases hh147 : ns = 147
  · subst hh147; exact nativeHeatGenNum_147_Gen
  by_cases hh148 : ns = 148
  · subst hh148; exact nativeHeatGenNum_148_Gen
  by_cases hh149 : ns = 149
  · subst hh149; exact nativeHeatGenNum_149_Gen
  by_cases hh150 : ns = 150
  · subst hh150; exact nativeHeatGenNum_150_Gen
  by_cases hh151 : ns = 151
  · subst hh151; exact nativeHeatGenNum_151_Gen
  by_cases hh152 : ns = 152
  · subst hh152; exact nativeHeatGenNum_152_Gen
  by_cases hh153 : ns = 153
  · subst hh153; exact nativeHeatGenNum_153_Gen
  by_cases hh154 : ns = 154
  · subst hh154; exact nativeHeatGenNum_154_Gen
  by_cases hh155 : ns = 155
  · subst hh155; exact nativeHeatGenNum_155_Gen
  by_cases hh156 : ns = 156
  · subst hh156; exact nativeHeatGenNum_156_Gen
  by_cases hh157 : ns = 157
  · subst hh157; exact nativeHeatGenNum_157_Gen
  by_cases hh158 : ns = 158
  · subst hh158; exact nativeHeatGenNum_158_Gen
  by_cases hh159 : ns = 159
  · subst hh159; exact nativeHeatGenNum_159_Gen
  have hh : ns = 160 := by omega
  subst hh; exact nativeHeatGenNum_160_Gen

end ASDExplicitGamma.Native
