module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong1184Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1193).2.2,
  nativeAvg*nativeA+(nativeRaw 1194).2.2,
  nativeAvg*nativeA+(nativeRaw 1195).2.2,
  nativeAvg*nativeA+(nativeRaw 1196).2.2,
  nativeAvg*nativeA+(nativeRaw 1197).2.2,
  nativeAvg*nativeA+(nativeRaw 1198).2.2,
  nativeAvg*nativeA+(nativeRaw 1199).2.2,
  nativeAvg*nativeA+(nativeRaw 1200).2.2,
  nativeAvg*nativeA+(nativeRaw 1201).2.2,
  nativeAvg*nativeA+(nativeRaw 1202).2.2,
  nativeAvg*nativeA+(nativeRaw 1203).2.2,
  nativeAvg*nativeA+(nativeRaw 1204).2.2,
  nativeAvg*nativeA+(nativeRaw 1205).2.2,
  nativeAvg*nativeA+(nativeRaw 1206).2.2,
  nativeAvg*nativeA+(nativeRaw 1207).2.2,
  nativeAvg*nativeA+(nativeRaw 1208).2.2,
  nativeAvg*nativeA+(nativeRaw 1209).2.2,
  nativeAvg*nativeA+(nativeRaw 1210).2.2,
  nativeAvg*nativeA+(nativeRaw 1211).2.2,
  nativeAvg*nativeA+(nativeRaw 1212).2.2,
  nativeAvg*nativeA+(nativeRaw 1213).2.2,
  nativeAvg*nativeA+(nativeRaw 1214).2.2,
  nativeAvg*nativeA+(nativeRaw 1215).2.2,
  nativeAvg*nativeA+(nativeRaw 1216).2.2,
  nativeAvg*nativeA+(nativeRaw 1217).2.2,
  nativeAvg*nativeA+(nativeRaw 1218).2.2,
  nativeAvg*nativeA+(nativeRaw 1219).2.2,
  nativeAvg*nativeA+(nativeRaw 1220).2.2,
  nativeAvg*nativeA+(nativeRaw 1221).2.2,
  nativeAvg*nativeA+(nativeRaw 1222).2.2,
  nativeAvg*nativeA+(nativeRaw 1223).2.2,
  nativeAvg*nativeA+(nativeRaw 1224).2.2
]

def nativeHistoryStrong1184Start : ℚ × ℚ := ((458360157377083/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531329181390428778790894394796394947640402004920933272719661817607566261082518410397330024044021/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong1184End : ℚ × ℚ := ((9399069787053/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(594691416147673803597348861799349549368455050250615116659089957727200945782637683165962614471711403/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong1184Inputs_length : nativeHistoryStrong1184Inputs.length = 32 := rfl

theorem nativeHistoryStrong1184Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1193+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1193+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong1184Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong1184Inputs.getD i.val 0)*(nativeHistoryStrong1184Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong1184_checked : nativeHistorySteps 9 1184 32 nativeHistoryStrong1184Inputs nativeHistoryStrong1184Start = nativeHistoryStrong1184End := by
  decide +kernel

theorem nativeHistoryStrong1184Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong1184Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong1184Weight : nativeHistoryRatio^1184 ≤ nativeHistoryStrong1184Start.1 := by
  decide +kernel

theorem nativeHistoryStrong1184Real_bound : nativeHistoryReal 9 1184 nativeHistoryStrong1184Inputs ≤ (nativeHistoryStrong1184End.2 : ℝ)-(nativeHistoryStrong1184Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong1184Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong1184Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong1184Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong1184Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong1184Inputs.length) := nativeHistoryStrong1184Domains ⟨i,by simpa only [nativeHistoryStrong1184Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong1184Inputs.length) := nativeHistoryStrong1184Roots ⟨i,by simpa only [nativeHistoryStrong1184Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong1184Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 1184 nativeHistoryStrong1184Inputs nativeHistoryStrong1184Start ht hd hr hw
  simpa only [nativeHistoryStrong1184Inputs_length,nativeHistoryStrong1184_checked] using hs

end ASDExplicitGamma.Numerics.Native
