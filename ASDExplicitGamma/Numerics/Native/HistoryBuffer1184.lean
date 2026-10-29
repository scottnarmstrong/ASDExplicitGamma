module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer1184Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1233).2.2,
  nativeAvg*nativeA+(nativeRaw 1234).2.2,
  nativeAvg*nativeA+(nativeRaw 1235).2.2,
  nativeAvg*nativeA+(nativeRaw 1236).2.2,
  nativeAvg*nativeA+(nativeRaw 1237).2.2,
  nativeAvg*nativeA+(nativeRaw 1238).2.2,
  nativeAvg*nativeA+(nativeRaw 1239).2.2,
  nativeAvg*nativeA+(nativeRaw 1240).2.2,
  nativeAvg*nativeA+(nativeRaw 1241).2.2,
  nativeAvg*nativeA+(nativeRaw 1242).2.2,
  nativeAvg*nativeA+(nativeRaw 1243).2.2,
  nativeAvg*nativeA+(nativeRaw 1244).2.2,
  nativeAvg*nativeA+(nativeRaw 1245).2.2,
  nativeAvg*nativeA+(nativeRaw 1246).2.2,
  nativeAvg*nativeA+(nativeRaw 1247).2.2,
  nativeAvg*nativeA+(nativeRaw 1248).2.2,
  nativeAvg*nativeA+(nativeRaw 1249).2.2,
  nativeAvg*nativeA+(nativeRaw 1250).2.2,
  nativeAvg*nativeA+(nativeRaw 1251).2.2,
  nativeAvg*nativeA+(nativeRaw 1252).2.2,
  nativeAvg*nativeA+(nativeRaw 1253).2.2,
  nativeAvg*nativeA+(nativeRaw 1254).2.2,
  nativeAvg*nativeA+(nativeRaw 1255).2.2,
  nativeAvg*nativeA+(nativeRaw 1256).2.2,
  nativeAvg*nativeA+(nativeRaw 1257).2.2,
  nativeAvg*nativeA+(nativeRaw 1258).2.2,
  nativeAvg*nativeA+(nativeRaw 1259).2.2,
  nativeAvg*nativeA+(nativeRaw 1260).2.2,
  nativeAvg*nativeA+(nativeRaw 1261).2.2,
  nativeAvg*nativeA+(nativeRaw 1262).2.2,
  nativeAvg*nativeA+(nativeRaw 1263).2.2,
  nativeAvg*nativeA+(nativeRaw 1264).2.2
]

def nativeHistoryBuffer1184Start : ℚ × ℚ := ((458360157377083/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457369991457740012773467065042303/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer1184End : ℚ × ℚ := ((9399069787053/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457369991567795565168323926225753/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer1184Inputs_length : nativeHistoryBuffer1184Inputs.length = 32 := rfl

theorem nativeHistoryBuffer1184Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1233+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1233+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer1184Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer1184Inputs.getD i.val 0)*(nativeHistoryBuffer1184Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer1184_checked : nativeHistorySteps 49 1184 32 nativeHistoryBuffer1184Inputs nativeHistoryBuffer1184Start = nativeHistoryBuffer1184End := by
  decide +kernel

theorem nativeHistoryBuffer1184Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer1184Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer1184Weight : nativeHistoryRatio^1184 ≤ nativeHistoryBuffer1184Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer1184Real_bound : nativeHistoryReal 49 1184 nativeHistoryBuffer1184Inputs ≤ (nativeHistoryBuffer1184End.2 : ℝ)-(nativeHistoryBuffer1184Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer1184Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer1184Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer1184Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer1184Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer1184Inputs.length) := nativeHistoryBuffer1184Domains ⟨i,by simpa only [nativeHistoryBuffer1184Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer1184Inputs.length) := nativeHistoryBuffer1184Roots ⟨i,by simpa only [nativeHistoryBuffer1184Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer1184Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 1184 nativeHistoryBuffer1184Inputs nativeHistoryBuffer1184Start ht hd hr hw
  simpa only [nativeHistoryBuffer1184Inputs_length,nativeHistoryBuffer1184_checked] using hs

end ASDExplicitGamma.Numerics.Native
