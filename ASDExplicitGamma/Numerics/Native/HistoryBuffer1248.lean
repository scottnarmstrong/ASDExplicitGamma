module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer1248Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1297).2.2,
  nativeAvg*nativeA+(nativeRaw 1298).2.2,
  nativeAvg*nativeA+(nativeRaw 1299).2.2,
  nativeAvg*nativeA+(nativeRaw 1300).2.2,
  nativeAvg*nativeA+(nativeRaw 1301).2.2,
  nativeAvg*nativeA+(nativeRaw 1302).2.2,
  nativeAvg*nativeA+(nativeRaw 1303).2.2,
  nativeAvg*nativeA+(nativeRaw 1304).2.2,
  nativeAvg*nativeA+(nativeRaw 1305).2.2,
  nativeAvg*nativeA+(nativeRaw 1306).2.2,
  nativeAvg*nativeA+(nativeRaw 1307).2.2,
  nativeAvg*nativeA+(nativeRaw 1308).2.2,
  nativeAvg*nativeA+(nativeRaw 1309).2.2,
  nativeAvg*nativeA+(nativeRaw 1310).2.2,
  nativeAvg*nativeA+(nativeRaw 1311).2.2,
  nativeAvg*nativeA+(nativeRaw 1312).2.2,
  nativeAvg*nativeA+(nativeRaw 1313).2.2,
  nativeAvg*nativeA+(nativeRaw 1314).2.2,
  nativeAvg*nativeA+(nativeRaw 1315).2.2,
  nativeAvg*nativeA+(nativeRaw 1316).2.2,
  nativeAvg*nativeA+(nativeRaw 1317).2.2,
  nativeAvg*nativeA+(nativeRaw 1318).2.2,
  nativeAvg*nativeA+(nativeRaw 1319).2.2,
  nativeAvg*nativeA+(nativeRaw 1320).2.2,
  nativeAvg*nativeA+(nativeRaw 1321).2.2,
  nativeAvg*nativeA+(nativeRaw 1322).2.2,
  nativeAvg*nativeA+(nativeRaw 1323).2.2,
  nativeAvg*nativeA+(nativeRaw 1324).2.2,
  nativeAvg*nativeA+(nativeRaw 1325).2.2,
  nativeAvg*nativeA+(nativeRaw 1326).2.2,
  nativeAvg*nativeA+(nativeRaw 1327).2.2,
  nativeAvg*nativeA+(nativeRaw 1328).2.2
]

def nativeHistoryBuffer1248Start : ℚ × ℚ := ((24092002611/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457369991569752981083686468350333/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer1248End : ℚ × ℚ := ((123506817/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(14641580925849106226701415786384343621134619778273363930341733750298364342497892465652216960266779171/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer1248Inputs_length : nativeHistoryBuffer1248Inputs.length = 32 := rfl

theorem nativeHistoryBuffer1248Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1297+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1297+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer1248Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer1248Inputs.getD i.val 0)*(nativeHistoryBuffer1248Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer1248_checked : nativeHistorySteps 49 1248 32 nativeHistoryBuffer1248Inputs nativeHistoryBuffer1248Start = nativeHistoryBuffer1248End := by
  decide +kernel

theorem nativeHistoryBuffer1248Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer1248Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer1248Weight : nativeHistoryRatio^1248 ≤ nativeHistoryBuffer1248Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer1248Real_bound : nativeHistoryReal 49 1248 nativeHistoryBuffer1248Inputs ≤ (nativeHistoryBuffer1248End.2 : ℝ)-(nativeHistoryBuffer1248Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer1248Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer1248Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer1248Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer1248Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer1248Inputs.length) := nativeHistoryBuffer1248Domains ⟨i,by simpa only [nativeHistoryBuffer1248Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer1248Inputs.length) := nativeHistoryBuffer1248Roots ⟨i,by simpa only [nativeHistoryBuffer1248Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer1248Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 1248 nativeHistoryBuffer1248Inputs nativeHistoryBuffer1248Start ht hd hr hw
  simpa only [nativeHistoryBuffer1248Inputs_length,nativeHistoryBuffer1248_checked] using hs

end ASDExplicitGamma.Numerics.Native
