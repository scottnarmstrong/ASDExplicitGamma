module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer1216Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1265).2.2,
  nativeAvg*nativeA+(nativeRaw 1266).2.2,
  nativeAvg*nativeA+(nativeRaw 1267).2.2,
  nativeAvg*nativeA+(nativeRaw 1268).2.2,
  nativeAvg*nativeA+(nativeRaw 1269).2.2,
  nativeAvg*nativeA+(nativeRaw 1270).2.2,
  nativeAvg*nativeA+(nativeRaw 1271).2.2,
  nativeAvg*nativeA+(nativeRaw 1272).2.2,
  nativeAvg*nativeA+(nativeRaw 1273).2.2,
  nativeAvg*nativeA+(nativeRaw 1274).2.2,
  nativeAvg*nativeA+(nativeRaw 1275).2.2,
  nativeAvg*nativeA+(nativeRaw 1276).2.2,
  nativeAvg*nativeA+(nativeRaw 1277).2.2,
  nativeAvg*nativeA+(nativeRaw 1278).2.2,
  nativeAvg*nativeA+(nativeRaw 1279).2.2,
  nativeAvg*nativeA+(nativeRaw 1280).2.2,
  nativeAvg*nativeA+(nativeRaw 1281).2.2,
  nativeAvg*nativeA+(nativeRaw 1282).2.2,
  nativeAvg*nativeA+(nativeRaw 1283).2.2,
  nativeAvg*nativeA+(nativeRaw 1284).2.2,
  nativeAvg*nativeA+(nativeRaw 1285).2.2,
  nativeAvg*nativeA+(nativeRaw 1286).2.2,
  nativeAvg*nativeA+(nativeRaw 1287).2.2,
  nativeAvg*nativeA+(nativeRaw 1288).2.2,
  nativeAvg*nativeA+(nativeRaw 1289).2.2,
  nativeAvg*nativeA+(nativeRaw 1290).2.2,
  nativeAvg*nativeA+(nativeRaw 1291).2.2,
  nativeAvg*nativeA+(nativeRaw 1292).2.2,
  nativeAvg*nativeA+(nativeRaw 1293).2.2,
  nativeAvg*nativeA+(nativeRaw 1294).2.2,
  nativeAvg*nativeA+(nativeRaw 1295).2.2,
  nativeAvg*nativeA+(nativeRaw 1296).2.2
]

def nativeHistoryBuffer1216Start : ℚ × ℚ := ((9399069787053/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457369991567795565168323926225753/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer1216End : ℚ × ℚ := ((24092002611/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457369991569752981083686468350333/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer1216Inputs_length : nativeHistoryBuffer1216Inputs.length = 32 := rfl

theorem nativeHistoryBuffer1216Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1265+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1265+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer1216Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer1216Inputs.getD i.val 0)*(nativeHistoryBuffer1216Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer1216_checked : nativeHistorySteps 49 1216 32 nativeHistoryBuffer1216Inputs nativeHistoryBuffer1216Start = nativeHistoryBuffer1216End := by
  decide +kernel

theorem nativeHistoryBuffer1216Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer1216Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer1216Weight : nativeHistoryRatio^1216 ≤ nativeHistoryBuffer1216Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer1216Real_bound : nativeHistoryReal 49 1216 nativeHistoryBuffer1216Inputs ≤ (nativeHistoryBuffer1216End.2 : ℝ)-(nativeHistoryBuffer1216Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer1216Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer1216Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer1216Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer1216Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer1216Inputs.length) := nativeHistoryBuffer1216Domains ⟨i,by simpa only [nativeHistoryBuffer1216Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer1216Inputs.length) := nativeHistoryBuffer1216Roots ⟨i,by simpa only [nativeHistoryBuffer1216Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer1216Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 1216 nativeHistoryBuffer1216Inputs nativeHistoryBuffer1216Start ht hd hr hw
  simpa only [nativeHistoryBuffer1216Inputs_length,nativeHistoryBuffer1216_checked] using hs

end ASDExplicitGamma.Numerics.Native
