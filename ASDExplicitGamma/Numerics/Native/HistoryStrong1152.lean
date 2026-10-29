module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong1152Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1161).2.2,
  nativeAvg*nativeA+(nativeRaw 1162).2.2,
  nativeAvg*nativeA+(nativeRaw 1163).2.2,
  nativeAvg*nativeA+(nativeRaw 1164).2.2,
  nativeAvg*nativeA+(nativeRaw 1165).2.2,
  nativeAvg*nativeA+(nativeRaw 1166).2.2,
  nativeAvg*nativeA+(nativeRaw 1167).2.2,
  nativeAvg*nativeA+(nativeRaw 1168).2.2,
  nativeAvg*nativeA+(nativeRaw 1169).2.2,
  nativeAvg*nativeA+(nativeRaw 1170).2.2,
  nativeAvg*nativeA+(nativeRaw 1171).2.2,
  nativeAvg*nativeA+(nativeRaw 1172).2.2,
  nativeAvg*nativeA+(nativeRaw 1173).2.2,
  nativeAvg*nativeA+(nativeRaw 1174).2.2,
  nativeAvg*nativeA+(nativeRaw 1175).2.2,
  nativeAvg*nativeA+(nativeRaw 1176).2.2,
  nativeAvg*nativeA+(nativeRaw 1177).2.2,
  nativeAvg*nativeA+(nativeRaw 1178).2.2,
  nativeAvg*nativeA+(nativeRaw 1179).2.2,
  nativeAvg*nativeA+(nativeRaw 1180).2.2,
  nativeAvg*nativeA+(nativeRaw 1181).2.2,
  nativeAvg*nativeA+(nativeRaw 1182).2.2,
  nativeAvg*nativeA+(nativeRaw 1183).2.2,
  nativeAvg*nativeA+(nativeRaw 1184).2.2,
  nativeAvg*nativeA+(nativeRaw 1185).2.2,
  nativeAvg*nativeA+(nativeRaw 1186).2.2,
  nativeAvg*nativeA+(nativeRaw 1187).2.2,
  nativeAvg*nativeA+(nativeRaw 1188).2.2,
  nativeAvg*nativeA+(nativeRaw 1189).2.2,
  nativeAvg*nativeA+(nativeRaw 1190).2.2,
  nativeAvg*nativeA+(nativeRaw 1191).2.2,
  nativeAvg*nativeA+(nativeRaw 1192).2.2
]

def nativeHistoryStrong1152Start : ℚ × ℚ := ((178821129010214211/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323635215132518310011202840425977166111/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong1152End : ℚ × ℚ := ((458360157377083/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390428778790894394796394947640402004920933272719661817607566261082518410397330024044021/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong1152Inputs_length : nativeHistoryStrong1152Inputs.length = 32 := rfl

theorem nativeHistoryStrong1152Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1161+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1161+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong1152Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong1152Inputs.getD i.val 0)*(nativeHistoryStrong1152Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong1152_checked : nativeHistorySteps 9 1152 32 nativeHistoryStrong1152Inputs nativeHistoryStrong1152Start = nativeHistoryStrong1152End := by
  decide +kernel

theorem nativeHistoryStrong1152Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong1152Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong1152Weight : nativeHistoryRatio^1152 ≤ nativeHistoryStrong1152Start.1 := by
  decide +kernel

theorem nativeHistoryStrong1152Real_bound : nativeHistoryReal 9 1152 nativeHistoryStrong1152Inputs ≤ (nativeHistoryStrong1152End.2 : ℝ)-(nativeHistoryStrong1152Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong1152Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong1152Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong1152Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong1152Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong1152Inputs.length) := nativeHistoryStrong1152Domains ⟨i,by simpa only [nativeHistoryStrong1152Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong1152Inputs.length) := nativeHistoryStrong1152Roots ⟨i,by simpa only [nativeHistoryStrong1152Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong1152Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 1152 nativeHistoryStrong1152Inputs nativeHistoryStrong1152Start ht hd hr hw
  simpa only [nativeHistoryStrong1152Inputs_length,nativeHistoryStrong1152_checked] using hs

end ASDExplicitGamma.Numerics.Native
