module

public import ASDExplicitGamma.Native.HeatInitialNumericsDataGen
public import ASDExplicitGamma.Numerics.Native.Heat009Initial
public import ASDExplicitGamma.Numerics.Native.Heat010Initial
public import ASDExplicitGamma.Numerics.Native.Heat011Initial
public import ASDExplicitGamma.Numerics.Native.Heat012Initial
public import ASDExplicitGamma.Numerics.Native.Heat013Initial
public import ASDExplicitGamma.Numerics.Native.Heat014Initial
public import ASDExplicitGamma.Numerics.Native.Heat015Initial
public import ASDExplicitGamma.Numerics.Native.Heat016Initial
public import ASDExplicitGamma.Numerics.Native.Heat017Initial
public import ASDExplicitGamma.Numerics.Native.Heat018Initial
public import ASDExplicitGamma.Numerics.Native.Heat019Initial
public import ASDExplicitGamma.Numerics.Native.Heat020Initial
public import ASDExplicitGamma.Numerics.Native.Heat021Initial
public import ASDExplicitGamma.Numerics.Native.Heat022Initial
public import ASDExplicitGamma.Numerics.Native.Heat023Initial
public import ASDExplicitGamma.Numerics.Native.Heat024Initial
public import ASDExplicitGamma.Numerics.Native.Heat025Initial
public import ASDExplicitGamma.Numerics.Native.Heat026Initial
public import ASDExplicitGamma.Numerics.Native.Heat027Initial

/-! Numeric certificates of the `ns`-shell refined initial moment for `9 ≤ ns < 28`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

theorem nativeHeat009BaseOk_Gen : nativeHeatGenBaseOk nativeHeat009Qm = true := by
  decide +kernel

theorem nativeHeat009RootOk_Gen : nativeHeatGenRootOk nativeHeat009Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_9_Gen : NativeHeatGenNum 9 := by
  refine nativeHeatGenNum_of_data 9 (by norm_num) nativeGap010Old ?_
    nativeHeat009Variance nativeHeat009Spectral nativeHeat009Qm
    nativeHeat009Variance_formula nativeHeat009Qm_formula ?_ ?_ ?_ ?_
    nativeHeat009BaseOk_Gen nativeHeat009RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap010Old]
  · norm_num [nativeHeat009Variance]
  · norm_num [nativeHeat009Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat009Qm]

theorem nativeHeat010BaseOk_Gen : nativeHeatGenBaseOk nativeHeat010Qm = true := by
  decide +kernel

theorem nativeHeat010RootOk_Gen : nativeHeatGenRootOk nativeHeat010Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_10_Gen : NativeHeatGenNum 10 := by
  refine nativeHeatGenNum_of_data 10 (by norm_num) nativeGap011Old ?_
    nativeHeat010Variance nativeHeat010Spectral nativeHeat010Qm
    nativeHeat010Variance_formula nativeHeat010Qm_formula ?_ ?_ ?_ ?_
    nativeHeat010BaseOk_Gen nativeHeat010RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap011Old]
  · norm_num [nativeHeat010Variance]
  · norm_num [nativeHeat010Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat010Qm]

theorem nativeHeat011BaseOk_Gen : nativeHeatGenBaseOk nativeHeat011Qm = true := by
  decide +kernel

theorem nativeHeat011RootOk_Gen : nativeHeatGenRootOk nativeHeat011Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_11_Gen : NativeHeatGenNum 11 := by
  refine nativeHeatGenNum_of_data 11 (by norm_num) nativeGap012Old ?_
    nativeHeat011Variance nativeHeat011Spectral nativeHeat011Qm
    nativeHeat011Variance_formula nativeHeat011Qm_formula ?_ ?_ ?_ ?_
    nativeHeat011BaseOk_Gen nativeHeat011RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap012Old]
  · norm_num [nativeHeat011Variance]
  · norm_num [nativeHeat011Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat011Qm]

theorem nativeHeat012BaseOk_Gen : nativeHeatGenBaseOk nativeHeat012Qm = true := by
  decide +kernel

theorem nativeHeat012RootOk_Gen : nativeHeatGenRootOk nativeHeat012Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_12_Gen : NativeHeatGenNum 12 := by
  refine nativeHeatGenNum_of_data 12 (by norm_num) nativeGap013Old ?_
    nativeHeat012Variance nativeHeat012Spectral nativeHeat012Qm
    nativeHeat012Variance_formula nativeHeat012Qm_formula ?_ ?_ ?_ ?_
    nativeHeat012BaseOk_Gen nativeHeat012RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap013Old]
  · norm_num [nativeHeat012Variance]
  · norm_num [nativeHeat012Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat012Qm]

theorem nativeHeat013BaseOk_Gen : nativeHeatGenBaseOk nativeHeat013Qm = true := by
  decide +kernel

theorem nativeHeat013RootOk_Gen : nativeHeatGenRootOk nativeHeat013Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_13_Gen : NativeHeatGenNum 13 := by
  refine nativeHeatGenNum_of_data 13 (by norm_num) nativeGap014Old ?_
    nativeHeat013Variance nativeHeat013Spectral nativeHeat013Qm
    nativeHeat013Variance_formula nativeHeat013Qm_formula ?_ ?_ ?_ ?_
    nativeHeat013BaseOk_Gen nativeHeat013RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap014Old]
  · norm_num [nativeHeat013Variance]
  · norm_num [nativeHeat013Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat013Qm]

theorem nativeHeat014BaseOk_Gen : nativeHeatGenBaseOk nativeHeat014Qm = true := by
  decide +kernel

theorem nativeHeat014RootOk_Gen : nativeHeatGenRootOk nativeHeat014Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_14_Gen : NativeHeatGenNum 14 := by
  refine nativeHeatGenNum_of_data 14 (by norm_num) nativeGap015Old ?_
    nativeHeat014Variance nativeHeat014Spectral nativeHeat014Qm
    nativeHeat014Variance_formula nativeHeat014Qm_formula ?_ ?_ ?_ ?_
    nativeHeat014BaseOk_Gen nativeHeat014RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap015Old]
  · norm_num [nativeHeat014Variance]
  · norm_num [nativeHeat014Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat014Qm]

theorem nativeHeat015BaseOk_Gen : nativeHeatGenBaseOk nativeHeat015Qm = true := by
  decide +kernel

theorem nativeHeat015RootOk_Gen : nativeHeatGenRootOk nativeHeat015Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_15_Gen : NativeHeatGenNum 15 := by
  refine nativeHeatGenNum_of_data 15 (by norm_num) nativeGap016Old ?_
    nativeHeat015Variance nativeHeat015Spectral nativeHeat015Qm
    nativeHeat015Variance_formula nativeHeat015Qm_formula ?_ ?_ ?_ ?_
    nativeHeat015BaseOk_Gen nativeHeat015RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap016Old]
  · norm_num [nativeHeat015Variance]
  · norm_num [nativeHeat015Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat015Qm]

theorem nativeHeat016BaseOk_Gen : nativeHeatGenBaseOk nativeHeat016Qm = true := by
  decide +kernel

theorem nativeHeat016RootOk_Gen : nativeHeatGenRootOk nativeHeat016Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_16_Gen : NativeHeatGenNum 16 := by
  refine nativeHeatGenNum_of_data 16 (by norm_num) nativeGap017Old ?_
    nativeHeat016Variance nativeHeat016Spectral nativeHeat016Qm
    nativeHeat016Variance_formula nativeHeat016Qm_formula ?_ ?_ ?_ ?_
    nativeHeat016BaseOk_Gen nativeHeat016RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap017Old]
  · norm_num [nativeHeat016Variance]
  · norm_num [nativeHeat016Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat016Qm]

theorem nativeHeat017BaseOk_Gen : nativeHeatGenBaseOk nativeHeat017Qm = true := by
  decide +kernel

theorem nativeHeat017RootOk_Gen : nativeHeatGenRootOk nativeHeat017Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_17_Gen : NativeHeatGenNum 17 := by
  refine nativeHeatGenNum_of_data 17 (by norm_num) nativeGap018Old ?_
    nativeHeat017Variance nativeHeat017Spectral nativeHeat017Qm
    nativeHeat017Variance_formula nativeHeat017Qm_formula ?_ ?_ ?_ ?_
    nativeHeat017BaseOk_Gen nativeHeat017RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap018Old]
  · norm_num [nativeHeat017Variance]
  · norm_num [nativeHeat017Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat017Qm]

theorem nativeHeat018BaseOk_Gen : nativeHeatGenBaseOk nativeHeat018Qm = true := by
  decide +kernel

theorem nativeHeat018RootOk_Gen : nativeHeatGenRootOk nativeHeat018Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_18_Gen : NativeHeatGenNum 18 := by
  refine nativeHeatGenNum_of_data 18 (by norm_num) nativeGap019Old ?_
    nativeHeat018Variance nativeHeat018Spectral nativeHeat018Qm
    nativeHeat018Variance_formula nativeHeat018Qm_formula ?_ ?_ ?_ ?_
    nativeHeat018BaseOk_Gen nativeHeat018RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap019Old]
  · norm_num [nativeHeat018Variance]
  · norm_num [nativeHeat018Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat018Qm]

theorem nativeHeat019BaseOk_Gen : nativeHeatGenBaseOk nativeHeat019Qm = true := by
  decide +kernel

theorem nativeHeat019RootOk_Gen : nativeHeatGenRootOk nativeHeat019Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_19_Gen : NativeHeatGenNum 19 := by
  refine nativeHeatGenNum_of_data 19 (by norm_num) nativeGap020Old ?_
    nativeHeat019Variance nativeHeat019Spectral nativeHeat019Qm
    nativeHeat019Variance_formula nativeHeat019Qm_formula ?_ ?_ ?_ ?_
    nativeHeat019BaseOk_Gen nativeHeat019RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap020Old]
  · norm_num [nativeHeat019Variance]
  · norm_num [nativeHeat019Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat019Qm]

theorem nativeHeat020BaseOk_Gen : nativeHeatGenBaseOk nativeHeat020Qm = true := by
  decide +kernel

theorem nativeHeat020RootOk_Gen : nativeHeatGenRootOk nativeHeat020Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_20_Gen : NativeHeatGenNum 20 := by
  refine nativeHeatGenNum_of_data 20 (by norm_num) nativeGap021Old ?_
    nativeHeat020Variance nativeHeat020Spectral nativeHeat020Qm
    nativeHeat020Variance_formula nativeHeat020Qm_formula ?_ ?_ ?_ ?_
    nativeHeat020BaseOk_Gen nativeHeat020RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap021Old]
  · norm_num [nativeHeat020Variance]
  · norm_num [nativeHeat020Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat020Qm]

theorem nativeHeat021BaseOk_Gen : nativeHeatGenBaseOk nativeHeat021Qm = true := by
  decide +kernel

theorem nativeHeat021RootOk_Gen : nativeHeatGenRootOk nativeHeat021Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_21_Gen : NativeHeatGenNum 21 := by
  refine nativeHeatGenNum_of_data 21 (by norm_num) nativeGap022Old ?_
    nativeHeat021Variance nativeHeat021Spectral nativeHeat021Qm
    nativeHeat021Variance_formula nativeHeat021Qm_formula ?_ ?_ ?_ ?_
    nativeHeat021BaseOk_Gen nativeHeat021RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap022Old]
  · norm_num [nativeHeat021Variance]
  · norm_num [nativeHeat021Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat021Qm]

theorem nativeHeat022BaseOk_Gen : nativeHeatGenBaseOk nativeHeat022Qm = true := by
  decide +kernel

theorem nativeHeat022RootOk_Gen : nativeHeatGenRootOk nativeHeat022Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_22_Gen : NativeHeatGenNum 22 := by
  refine nativeHeatGenNum_of_data 22 (by norm_num) nativeGap023Old ?_
    nativeHeat022Variance nativeHeat022Spectral nativeHeat022Qm
    nativeHeat022Variance_formula nativeHeat022Qm_formula ?_ ?_ ?_ ?_
    nativeHeat022BaseOk_Gen nativeHeat022RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap023Old]
  · norm_num [nativeHeat022Variance]
  · norm_num [nativeHeat022Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat022Qm]

theorem nativeHeat023BaseOk_Gen : nativeHeatGenBaseOk nativeHeat023Qm = true := by
  decide +kernel

theorem nativeHeat023RootOk_Gen : nativeHeatGenRootOk nativeHeat023Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_23_Gen : NativeHeatGenNum 23 := by
  refine nativeHeatGenNum_of_data 23 (by norm_num) nativeGap024Old ?_
    nativeHeat023Variance nativeHeat023Spectral nativeHeat023Qm
    nativeHeat023Variance_formula nativeHeat023Qm_formula ?_ ?_ ?_ ?_
    nativeHeat023BaseOk_Gen nativeHeat023RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap024Old]
  · norm_num [nativeHeat023Variance]
  · norm_num [nativeHeat023Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat023Qm]

theorem nativeHeat024BaseOk_Gen : nativeHeatGenBaseOk nativeHeat024Qm = true := by
  decide +kernel

theorem nativeHeat024RootOk_Gen : nativeHeatGenRootOk nativeHeat024Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_24_Gen : NativeHeatGenNum 24 := by
  refine nativeHeatGenNum_of_data 24 (by norm_num) nativeGap025Old ?_
    nativeHeat024Variance nativeHeat024Spectral nativeHeat024Qm
    nativeHeat024Variance_formula nativeHeat024Qm_formula ?_ ?_ ?_ ?_
    nativeHeat024BaseOk_Gen nativeHeat024RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap025Old]
  · norm_num [nativeHeat024Variance]
  · norm_num [nativeHeat024Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat024Qm]

theorem nativeHeat025BaseOk_Gen : nativeHeatGenBaseOk nativeHeat025Qm = true := by
  decide +kernel

theorem nativeHeat025RootOk_Gen : nativeHeatGenRootOk nativeHeat025Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_25_Gen : NativeHeatGenNum 25 := by
  refine nativeHeatGenNum_of_data 25 (by norm_num) nativeGap026Old ?_
    nativeHeat025Variance nativeHeat025Spectral nativeHeat025Qm
    nativeHeat025Variance_formula nativeHeat025Qm_formula ?_ ?_ ?_ ?_
    nativeHeat025BaseOk_Gen nativeHeat025RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap026Old]
  · norm_num [nativeHeat025Variance]
  · norm_num [nativeHeat025Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat025Qm]

theorem nativeHeat026BaseOk_Gen : nativeHeatGenBaseOk nativeHeat026Qm = true := by
  decide +kernel

theorem nativeHeat026RootOk_Gen : nativeHeatGenRootOk nativeHeat026Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_26_Gen : NativeHeatGenNum 26 := by
  refine nativeHeatGenNum_of_data 26 (by norm_num) nativeGap027Old ?_
    nativeHeat026Variance nativeHeat026Spectral nativeHeat026Qm
    nativeHeat026Variance_formula nativeHeat026Qm_formula ?_ ?_ ?_ ?_
    nativeHeat026BaseOk_Gen nativeHeat026RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap027Old]
  · norm_num [nativeHeat026Variance]
  · norm_num [nativeHeat026Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat026Qm]

theorem nativeHeat027BaseOk_Gen : nativeHeatGenBaseOk nativeHeat027Qm = true := by
  decide +kernel

theorem nativeHeat027RootOk_Gen : nativeHeatGenRootOk nativeHeat027Qm = true := by
  decide +kernel

theorem nativeHeatGenNum_27_Gen : NativeHeatGenNum 27 := by
  refine nativeHeatGenNum_of_data 27 (by norm_num) nativeGap028Old ?_
    nativeHeat027Variance nativeHeat027Spectral nativeHeat027Qm
    nativeHeat027Variance_formula nativeHeat027Qm_formula ?_ ?_ ?_ ?_
    nativeHeat027BaseOk_Gen nativeHeat027RootOk_Gen
  · unfold nativeHeatOldRowGen
    rfl
  · unfold nativeHeatGenEUpper
    norm_num [Finset.sum_range_succ, Nat.factorial, nativeGap028Old]
  · norm_num [nativeHeat027Variance]
  · norm_num [nativeHeat027Spectral]
  · intro j hj
    interval_cases j <;> norm_num [nativeHeat027Qm]

theorem nativeHeatGenNum_range1_Gen (ns : ℕ) (h1 : 9 ≤ ns) (h2 : ns < 28) :
    NativeHeatGenNum ns := by
  by_cases hh9 : ns = 9
  · subst hh9; exact nativeHeatGenNum_9_Gen
  by_cases hh10 : ns = 10
  · subst hh10; exact nativeHeatGenNum_10_Gen
  by_cases hh11 : ns = 11
  · subst hh11; exact nativeHeatGenNum_11_Gen
  by_cases hh12 : ns = 12
  · subst hh12; exact nativeHeatGenNum_12_Gen
  by_cases hh13 : ns = 13
  · subst hh13; exact nativeHeatGenNum_13_Gen
  by_cases hh14 : ns = 14
  · subst hh14; exact nativeHeatGenNum_14_Gen
  by_cases hh15 : ns = 15
  · subst hh15; exact nativeHeatGenNum_15_Gen
  by_cases hh16 : ns = 16
  · subst hh16; exact nativeHeatGenNum_16_Gen
  by_cases hh17 : ns = 17
  · subst hh17; exact nativeHeatGenNum_17_Gen
  by_cases hh18 : ns = 18
  · subst hh18; exact nativeHeatGenNum_18_Gen
  by_cases hh19 : ns = 19
  · subst hh19; exact nativeHeatGenNum_19_Gen
  by_cases hh20 : ns = 20
  · subst hh20; exact nativeHeatGenNum_20_Gen
  by_cases hh21 : ns = 21
  · subst hh21; exact nativeHeatGenNum_21_Gen
  by_cases hh22 : ns = 22
  · subst hh22; exact nativeHeatGenNum_22_Gen
  by_cases hh23 : ns = 23
  · subst hh23; exact nativeHeatGenNum_23_Gen
  by_cases hh24 : ns = 24
  · subst hh24; exact nativeHeatGenNum_24_Gen
  by_cases hh25 : ns = 25
  · subst hh25; exact nativeHeatGenNum_25_Gen
  by_cases hh26 : ns = 26
  · subst hh26; exact nativeHeatGenNum_26_Gen
  have hh : ns = 27 := by omega
  subst hh; exact nativeHeatGenNum_27_Gen

end ASDExplicitGamma.Native
