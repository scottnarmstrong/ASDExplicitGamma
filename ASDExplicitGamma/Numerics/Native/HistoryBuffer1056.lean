module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer1056Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1105).2.2,
  nativeAvg*nativeA+(nativeRaw 1106).2.2,
  nativeAvg*nativeA+(nativeRaw 1107).2.2,
  nativeAvg*nativeA+(nativeRaw 1108).2.2,
  nativeAvg*nativeA+(nativeRaw 1109).2.2,
  nativeAvg*nativeA+(nativeRaw 1110).2.2,
  nativeAvg*nativeA+(nativeRaw 1111).2.2,
  nativeAvg*nativeA+(nativeRaw 1112).2.2,
  nativeAvg*nativeA+(nativeRaw 1113).2.2,
  nativeAvg*nativeA+(nativeRaw 1114).2.2,
  nativeAvg*nativeA+(nativeRaw 1115).2.2,
  nativeAvg*nativeA+(nativeRaw 1116).2.2,
  nativeAvg*nativeA+(nativeRaw 1117).2.2,
  nativeAvg*nativeA+(nativeRaw 1118).2.2,
  nativeAvg*nativeA+(nativeRaw 1119).2.2,
  nativeAvg*nativeA+(nativeRaw 1120).2.2,
  nativeAvg*nativeA+(nativeRaw 1121).2.2,
  nativeAvg*nativeA+(nativeRaw 1122).2.2,
  nativeAvg*nativeA+(nativeRaw 1123).2.2,
  nativeAvg*nativeA+(nativeRaw 1124).2.2,
  nativeAvg*nativeA+(nativeRaw 1125).2.2,
  nativeAvg*nativeA+(nativeRaw 1126).2.2,
  nativeAvg*nativeA+(nativeRaw 1127).2.2,
  nativeAvg*nativeA+(nativeRaw 1128).2.2,
  nativeAvg*nativeA+(nativeRaw 1129).2.2,
  nativeAvg*nativeA+(nativeRaw 1130).2.2,
  nativeAvg*nativeA+(nativeRaw 1131).2.2,
  nativeAvg*nativeA+(nativeRaw 1132).2.2,
  nativeAvg*nativeA+(nativeRaw 1133).2.2,
  nativeAvg*nativeA+(nativeRaw 1134).2.2,
  nativeAvg*nativeA+(nativeRaw 1135).2.2,
  nativeAvg*nativeA+(nativeRaw 1136).2.2
]

def nativeHistoryBuffer1056Start : ℚ × ℚ := ((165910845491340978396069/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768687242269239556546727860683467500596722791842205694945226035456709269/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer1056End : ℚ × ℚ := ((6804289553110428999847/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457272151312315215234629553978297/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer1056Inputs_length : nativeHistoryBuffer1056Inputs.length = 32 := rfl

theorem nativeHistoryBuffer1056Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1105+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1105+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer1056Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer1056Inputs.getD i.val 0)*(nativeHistoryBuffer1056Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer1056_checked : nativeHistorySteps 49 1056 32 nativeHistoryBuffer1056Inputs nativeHistoryBuffer1056Start = nativeHistoryBuffer1056End := by
  decide +kernel

theorem nativeHistoryBuffer1056Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer1056Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer1056Weight : nativeHistoryRatio^1056 ≤ nativeHistoryBuffer1056Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer1056Real_bound : nativeHistoryReal 49 1056 nativeHistoryBuffer1056Inputs ≤ (nativeHistoryBuffer1056End.2 : ℝ)-(nativeHistoryBuffer1056Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer1056Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer1056Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer1056Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer1056Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer1056Inputs.length) := nativeHistoryBuffer1056Domains ⟨i,by simpa only [nativeHistoryBuffer1056Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer1056Inputs.length) := nativeHistoryBuffer1056Roots ⟨i,by simpa only [nativeHistoryBuffer1056Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer1056Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 1056 nativeHistoryBuffer1056Inputs nativeHistoryBuffer1056Start ht hd hr hw
  simpa only [nativeHistoryBuffer1056Inputs_length,nativeHistoryBuffer1056_checked] using hs

end ASDExplicitGamma.Numerics.Native
