module

public import ASDExplicitGamma.Native.HeatInitialNumericsDataGen
public import ASDExplicitGamma.Numerics.Native.Heat085Initial
public import ASDExplicitGamma.Numerics.Native.Heat086Initial
public import ASDExplicitGamma.Numerics.Native.Heat087Initial
public import ASDExplicitGamma.Numerics.Native.Heat088Initial
public import ASDExplicitGamma.Numerics.Native.Heat089Initial
public import ASDExplicitGamma.Numerics.Native.Heat090Initial
public import ASDExplicitGamma.Numerics.Native.Heat091Initial
public import ASDExplicitGamma.Numerics.Native.Heat092Initial
public import ASDExplicitGamma.Numerics.Native.Heat093Initial
public import ASDExplicitGamma.Numerics.Native.Heat094Initial
public import ASDExplicitGamma.Numerics.Native.Heat095Initial
public import ASDExplicitGamma.Numerics.Native.Heat096Initial
public import ASDExplicitGamma.Numerics.Native.Heat097Initial
public import ASDExplicitGamma.Numerics.Native.Heat098Initial
public import ASDExplicitGamma.Numerics.Native.Heat099Initial
public import ASDExplicitGamma.Numerics.Native.Heat100Initial
public import ASDExplicitGamma.Numerics.Native.Heat101Initial
public import ASDExplicitGamma.Numerics.Native.Heat102Initial
public import ASDExplicitGamma.Numerics.Native.Heat103Initial

/-! Numeric certificates of the `ns`-shell refined initial moment for `85 ≤ ns < 104`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

theorem nativeHeat085BaseOk_Gen : nativeHeatGenBaseOk nativeHeat085Qm = true := by
  decide +kernel

theorem nativeHeat085RootOk_Gen : nativeHeatGenRootOk nativeHeat085Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_85_Gen : NativeHeatGenNum 85 := by
  refine nativeHeatGenNum_of_data 85 (by norm_num) nativeGap086Old ?_
    nativeHeat085Variance nativeHeat085Spectral nativeHeat085Qm
    nativeHeat085Variance_formula nativeHeat085Qm_formula ?_ ?_ ?_ ?_
    nativeHeat085BaseOk_Gen nativeHeat085RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap086Old]
  · norm_num [nativeHeat085Variance]
  · norm_num [nativeHeat085Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat085Qm]

theorem nativeHeat086BaseOk_Gen : nativeHeatGenBaseOk nativeHeat086Qm = true := by
  decide +kernel

theorem nativeHeat086RootOk_Gen : nativeHeatGenRootOk nativeHeat086Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_86_Gen : NativeHeatGenNum 86 := by
  refine nativeHeatGenNum_of_data 86 (by norm_num) nativeGap087Old ?_
    nativeHeat086Variance nativeHeat086Spectral nativeHeat086Qm
    nativeHeat086Variance_formula nativeHeat086Qm_formula ?_ ?_ ?_ ?_
    nativeHeat086BaseOk_Gen nativeHeat086RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap087Old]
  · norm_num [nativeHeat086Variance]
  · norm_num [nativeHeat086Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat086Qm]

theorem nativeHeat087BaseOk_Gen : nativeHeatGenBaseOk nativeHeat087Qm = true := by
  decide +kernel

theorem nativeHeat087RootOk_Gen : nativeHeatGenRootOk nativeHeat087Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_87_Gen : NativeHeatGenNum 87 := by
  refine nativeHeatGenNum_of_data 87 (by norm_num) nativeGap088Old ?_
    nativeHeat087Variance nativeHeat087Spectral nativeHeat087Qm
    nativeHeat087Variance_formula nativeHeat087Qm_formula ?_ ?_ ?_ ?_
    nativeHeat087BaseOk_Gen nativeHeat087RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap088Old]
  · norm_num [nativeHeat087Variance]
  · norm_num [nativeHeat087Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat087Qm]

theorem nativeHeat088BaseOk_Gen : nativeHeatGenBaseOk nativeHeat088Qm = true := by
  decide +kernel

theorem nativeHeat088RootOk_Gen : nativeHeatGenRootOk nativeHeat088Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_88_Gen : NativeHeatGenNum 88 := by
  refine nativeHeatGenNum_of_data 88 (by norm_num) nativeGap089Old ?_
    nativeHeat088Variance nativeHeat088Spectral nativeHeat088Qm
    nativeHeat088Variance_formula nativeHeat088Qm_formula ?_ ?_ ?_ ?_
    nativeHeat088BaseOk_Gen nativeHeat088RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap089Old]
  · norm_num [nativeHeat088Variance]
  · norm_num [nativeHeat088Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat088Qm]

theorem nativeHeat089BaseOk_Gen : nativeHeatGenBaseOk nativeHeat089Qm = true := by
  decide +kernel

theorem nativeHeat089RootOk_Gen : nativeHeatGenRootOk nativeHeat089Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_89_Gen : NativeHeatGenNum 89 := by
  refine nativeHeatGenNum_of_data 89 (by norm_num) nativeGap090Old ?_
    nativeHeat089Variance nativeHeat089Spectral nativeHeat089Qm
    nativeHeat089Variance_formula nativeHeat089Qm_formula ?_ ?_ ?_ ?_
    nativeHeat089BaseOk_Gen nativeHeat089RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap090Old]
  · norm_num [nativeHeat089Variance]
  · norm_num [nativeHeat089Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat089Qm]

theorem nativeHeat090BaseOk_Gen : nativeHeatGenBaseOk nativeHeat090Qm = true := by
  decide +kernel

theorem nativeHeat090RootOk_Gen : nativeHeatGenRootOk nativeHeat090Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_90_Gen : NativeHeatGenNum 90 := by
  refine nativeHeatGenNum_of_data 90 (by norm_num) nativeGap091Old ?_
    nativeHeat090Variance nativeHeat090Spectral nativeHeat090Qm
    nativeHeat090Variance_formula nativeHeat090Qm_formula ?_ ?_ ?_ ?_
    nativeHeat090BaseOk_Gen nativeHeat090RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap091Old]
  · norm_num [nativeHeat090Variance]
  · norm_num [nativeHeat090Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat090Qm]

theorem nativeHeat091BaseOk_Gen : nativeHeatGenBaseOk nativeHeat091Qm = true := by
  decide +kernel

theorem nativeHeat091RootOk_Gen : nativeHeatGenRootOk nativeHeat091Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_91_Gen : NativeHeatGenNum 91 := by
  refine nativeHeatGenNum_of_data 91 (by norm_num) nativeGap092Old ?_
    nativeHeat091Variance nativeHeat091Spectral nativeHeat091Qm
    nativeHeat091Variance_formula nativeHeat091Qm_formula ?_ ?_ ?_ ?_
    nativeHeat091BaseOk_Gen nativeHeat091RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap092Old]
  · norm_num [nativeHeat091Variance]
  · norm_num [nativeHeat091Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat091Qm]

theorem nativeHeat092BaseOk_Gen : nativeHeatGenBaseOk nativeHeat092Qm = true := by
  decide +kernel

theorem nativeHeat092RootOk_Gen : nativeHeatGenRootOk nativeHeat092Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_92_Gen : NativeHeatGenNum 92 := by
  refine nativeHeatGenNum_of_data 92 (by norm_num) nativeGap093Old ?_
    nativeHeat092Variance nativeHeat092Spectral nativeHeat092Qm
    nativeHeat092Variance_formula nativeHeat092Qm_formula ?_ ?_ ?_ ?_
    nativeHeat092BaseOk_Gen nativeHeat092RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap093Old]
  · norm_num [nativeHeat092Variance]
  · norm_num [nativeHeat092Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat092Qm]

theorem nativeHeat093BaseOk_Gen : nativeHeatGenBaseOk nativeHeat093Qm = true := by
  decide +kernel

theorem nativeHeat093RootOk_Gen : nativeHeatGenRootOk nativeHeat093Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_93_Gen : NativeHeatGenNum 93 := by
  refine nativeHeatGenNum_of_data 93 (by norm_num) nativeGap094Old ?_
    nativeHeat093Variance nativeHeat093Spectral nativeHeat093Qm
    nativeHeat093Variance_formula nativeHeat093Qm_formula ?_ ?_ ?_ ?_
    nativeHeat093BaseOk_Gen nativeHeat093RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap094Old]
  · norm_num [nativeHeat093Variance]
  · norm_num [nativeHeat093Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat093Qm]

theorem nativeHeat094BaseOk_Gen : nativeHeatGenBaseOk nativeHeat094Qm = true := by
  decide +kernel

theorem nativeHeat094RootOk_Gen : nativeHeatGenRootOk nativeHeat094Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_94_Gen : NativeHeatGenNum 94 := by
  refine nativeHeatGenNum_of_data 94 (by norm_num) nativeGap095Old ?_
    nativeHeat094Variance nativeHeat094Spectral nativeHeat094Qm
    nativeHeat094Variance_formula nativeHeat094Qm_formula ?_ ?_ ?_ ?_
    nativeHeat094BaseOk_Gen nativeHeat094RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap095Old]
  · norm_num [nativeHeat094Variance]
  · norm_num [nativeHeat094Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat094Qm]

theorem nativeHeat095BaseOk_Gen : nativeHeatGenBaseOk nativeHeat095Qm = true := by
  decide +kernel

theorem nativeHeat095RootOk_Gen : nativeHeatGenRootOk nativeHeat095Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_95_Gen : NativeHeatGenNum 95 := by
  refine nativeHeatGenNum_of_data 95 (by norm_num) nativeGap096Old ?_
    nativeHeat095Variance nativeHeat095Spectral nativeHeat095Qm
    nativeHeat095Variance_formula nativeHeat095Qm_formula ?_ ?_ ?_ ?_
    nativeHeat095BaseOk_Gen nativeHeat095RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap096Old]
  · norm_num [nativeHeat095Variance]
  · norm_num [nativeHeat095Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat095Qm]

theorem nativeHeat096BaseOk_Gen : nativeHeatGenBaseOk nativeHeat096Qm = true := by
  decide +kernel

theorem nativeHeat096RootOk_Gen : nativeHeatGenRootOk nativeHeat096Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_96_Gen : NativeHeatGenNum 96 := by
  refine nativeHeatGenNum_of_data 96 (by norm_num) nativeGap097Old ?_
    nativeHeat096Variance nativeHeat096Spectral nativeHeat096Qm
    nativeHeat096Variance_formula nativeHeat096Qm_formula ?_ ?_ ?_ ?_
    nativeHeat096BaseOk_Gen nativeHeat096RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap097Old]
  · norm_num [nativeHeat096Variance]
  · norm_num [nativeHeat096Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat096Qm]

theorem nativeHeat097BaseOk_Gen : nativeHeatGenBaseOk nativeHeat097Qm = true := by
  decide +kernel

theorem nativeHeat097RootOk_Gen : nativeHeatGenRootOk nativeHeat097Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_97_Gen : NativeHeatGenNum 97 := by
  refine nativeHeatGenNum_of_data 97 (by norm_num) nativeGap098Old ?_
    nativeHeat097Variance nativeHeat097Spectral nativeHeat097Qm
    nativeHeat097Variance_formula nativeHeat097Qm_formula ?_ ?_ ?_ ?_
    nativeHeat097BaseOk_Gen nativeHeat097RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap098Old]
  · norm_num [nativeHeat097Variance]
  · norm_num [nativeHeat097Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat097Qm]

theorem nativeHeat098BaseOk_Gen : nativeHeatGenBaseOk nativeHeat098Qm = true := by
  decide +kernel

theorem nativeHeat098RootOk_Gen : nativeHeatGenRootOk nativeHeat098Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_98_Gen : NativeHeatGenNum 98 := by
  refine nativeHeatGenNum_of_data 98 (by norm_num) nativeGap099Old ?_
    nativeHeat098Variance nativeHeat098Spectral nativeHeat098Qm
    nativeHeat098Variance_formula nativeHeat098Qm_formula ?_ ?_ ?_ ?_
    nativeHeat098BaseOk_Gen nativeHeat098RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap099Old]
  · norm_num [nativeHeat098Variance]
  · norm_num [nativeHeat098Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat098Qm]

theorem nativeHeat099BaseOk_Gen : nativeHeatGenBaseOk nativeHeat099Qm = true := by
  decide +kernel

theorem nativeHeat099RootOk_Gen : nativeHeatGenRootOk nativeHeat099Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_99_Gen : NativeHeatGenNum 99 := by
  refine nativeHeatGenNum_of_data 99 (by norm_num) nativeGap100Old ?_
    nativeHeat099Variance nativeHeat099Spectral nativeHeat099Qm
    nativeHeat099Variance_formula nativeHeat099Qm_formula ?_ ?_ ?_ ?_
    nativeHeat099BaseOk_Gen nativeHeat099RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap100Old]
  · norm_num [nativeHeat099Variance]
  · norm_num [nativeHeat099Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat099Qm]

theorem nativeHeat100BaseOk_Gen : nativeHeatGenBaseOk nativeHeat100Qm = true := by
  decide +kernel

theorem nativeHeat100RootOk_Gen : nativeHeatGenRootOk nativeHeat100Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_100_Gen : NativeHeatGenNum 100 := by
  refine nativeHeatGenNum_of_data 100 (by norm_num) nativeGap101Old ?_
    nativeHeat100Variance nativeHeat100Spectral nativeHeat100Qm
    nativeHeat100Variance_formula nativeHeat100Qm_formula ?_ ?_ ?_ ?_
    nativeHeat100BaseOk_Gen nativeHeat100RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap101Old]
  · norm_num [nativeHeat100Variance]
  · norm_num [nativeHeat100Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat100Qm]

theorem nativeHeat101BaseOk_Gen : nativeHeatGenBaseOk nativeHeat101Qm = true := by
  decide +kernel

theorem nativeHeat101RootOk_Gen : nativeHeatGenRootOk nativeHeat101Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_101_Gen : NativeHeatGenNum 101 := by
  refine nativeHeatGenNum_of_data 101 (by norm_num) nativeGap102Old ?_
    nativeHeat101Variance nativeHeat101Spectral nativeHeat101Qm
    nativeHeat101Variance_formula nativeHeat101Qm_formula ?_ ?_ ?_ ?_
    nativeHeat101BaseOk_Gen nativeHeat101RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap102Old]
  · norm_num [nativeHeat101Variance]
  · norm_num [nativeHeat101Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat101Qm]

theorem nativeHeat102BaseOk_Gen : nativeHeatGenBaseOk nativeHeat102Qm = true := by
  decide +kernel

theorem nativeHeat102RootOk_Gen : nativeHeatGenRootOk nativeHeat102Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_102_Gen : NativeHeatGenNum 102 := by
  refine nativeHeatGenNum_of_data 102 (by norm_num) nativeGap103Old ?_
    nativeHeat102Variance nativeHeat102Spectral nativeHeat102Qm
    nativeHeat102Variance_formula nativeHeat102Qm_formula ?_ ?_ ?_ ?_
    nativeHeat102BaseOk_Gen nativeHeat102RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap103Old]
  · norm_num [nativeHeat102Variance]
  · norm_num [nativeHeat102Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat102Qm]

theorem nativeHeat103BaseOk_Gen : nativeHeatGenBaseOk nativeHeat103Qm = true := by
  decide +kernel

theorem nativeHeat103RootOk_Gen : nativeHeatGenRootOk nativeHeat103Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_103_Gen : NativeHeatGenNum 103 := by
  refine nativeHeatGenNum_of_data 103 (by norm_num) nativeGap104Old ?_
    nativeHeat103Variance nativeHeat103Spectral nativeHeat103Qm
    nativeHeat103Variance_formula nativeHeat103Qm_formula ?_ ?_ ?_ ?_
    nativeHeat103BaseOk_Gen nativeHeat103RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap104Old]
  · norm_num [nativeHeat103Variance]
  · norm_num [nativeHeat103Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat103Qm]

theorem nativeHeatGenNum_range5_Gen (ns : ℕ) (h1 : 85 ≤ ns) (h2 : ns < 104) :
    NativeHeatGenNum ns := by
  by_cases hh85 : ns = 85
  · subst hh85; exact nativeHeatGenNum_85_Gen
  by_cases hh86 : ns = 86
  · subst hh86; exact nativeHeatGenNum_86_Gen
  by_cases hh87 : ns = 87
  · subst hh87; exact nativeHeatGenNum_87_Gen
  by_cases hh88 : ns = 88
  · subst hh88; exact nativeHeatGenNum_88_Gen
  by_cases hh89 : ns = 89
  · subst hh89; exact nativeHeatGenNum_89_Gen
  by_cases hh90 : ns = 90
  · subst hh90; exact nativeHeatGenNum_90_Gen
  by_cases hh91 : ns = 91
  · subst hh91; exact nativeHeatGenNum_91_Gen
  by_cases hh92 : ns = 92
  · subst hh92; exact nativeHeatGenNum_92_Gen
  by_cases hh93 : ns = 93
  · subst hh93; exact nativeHeatGenNum_93_Gen
  by_cases hh94 : ns = 94
  · subst hh94; exact nativeHeatGenNum_94_Gen
  by_cases hh95 : ns = 95
  · subst hh95; exact nativeHeatGenNum_95_Gen
  by_cases hh96 : ns = 96
  · subst hh96; exact nativeHeatGenNum_96_Gen
  by_cases hh97 : ns = 97
  · subst hh97; exact nativeHeatGenNum_97_Gen
  by_cases hh98 : ns = 98
  · subst hh98; exact nativeHeatGenNum_98_Gen
  by_cases hh99 : ns = 99
  · subst hh99; exact nativeHeatGenNum_99_Gen
  by_cases hh100 : ns = 100
  · subst hh100; exact nativeHeatGenNum_100_Gen
  by_cases hh101 : ns = 101
  · subst hh101; exact nativeHeatGenNum_101_Gen
  by_cases hh102 : ns = 102
  · subst hh102; exact nativeHeatGenNum_102_Gen
  have hh : ns = 103 := by omega
  subst hh; exact nativeHeatGenNum_103_Gen

end ASDExplicitGamma.Native
