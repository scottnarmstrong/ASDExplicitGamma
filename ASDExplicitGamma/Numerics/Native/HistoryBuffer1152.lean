module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer1152Inputs : List ℚ := [
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
  nativeAvg*nativeA+(nativeRaw 1224).2.2,
  nativeAvg*nativeA+(nativeRaw 1225).2.2,
  nativeAvg*nativeA+(nativeRaw 1226).2.2,
  nativeAvg*nativeA+(nativeRaw 1227).2.2,
  nativeAvg*nativeA+(nativeRaw 1228).2.2,
  nativeAvg*nativeA+(nativeRaw 1229).2.2,
  nativeAvg*nativeA+(nativeRaw 1230).2.2,
  nativeAvg*nativeA+(nativeRaw 1231).2.2,
  nativeAvg*nativeA+(nativeRaw 1232).2.2
]

def nativeHistoryBuffer1152Start : ℚ × ℚ := ((178821129010214211/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(14641580925849106226701415786384343621134619778273363930341733750298364342495638655187170719060774311/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer1152End : ℚ × ℚ := ((458360157377083/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457369991457740012773467065042303/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer1152Inputs_length : nativeHistoryBuffer1152Inputs.length = 32 := rfl

theorem nativeHistoryBuffer1152Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1201+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1201+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer1152Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer1152Inputs.getD i.val 0)*(nativeHistoryBuffer1152Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer1152_checked : nativeHistorySteps 49 1152 32 nativeHistoryBuffer1152Inputs nativeHistoryBuffer1152Start = nativeHistoryBuffer1152End := by
  decide +kernel

theorem nativeHistoryBuffer1152Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer1152Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer1152Weight : nativeHistoryRatio^1152 ≤ nativeHistoryBuffer1152Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer1152Real_bound : nativeHistoryReal 49 1152 nativeHistoryBuffer1152Inputs ≤ (nativeHistoryBuffer1152End.2 : ℝ)-(nativeHistoryBuffer1152Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer1152Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer1152Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer1152Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer1152Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer1152Inputs.length) := nativeHistoryBuffer1152Domains ⟨i,by simpa only [nativeHistoryBuffer1152Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer1152Inputs.length) := nativeHistoryBuffer1152Roots ⟨i,by simpa only [nativeHistoryBuffer1152Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer1152Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 1152 nativeHistoryBuffer1152Inputs nativeHistoryBuffer1152Start ht hd hr hw
  simpa only [nativeHistoryBuffer1152Inputs_length,nativeHistoryBuffer1152_checked] using hs

end ASDExplicitGamma.Numerics.Native
