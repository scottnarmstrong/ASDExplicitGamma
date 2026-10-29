module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer1088Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1137).2.2,
  nativeAvg*nativeA+(nativeRaw 1138).2.2,
  nativeAvg*nativeA+(nativeRaw 1139).2.2,
  nativeAvg*nativeA+(nativeRaw 1140).2.2,
  nativeAvg*nativeA+(nativeRaw 1141).2.2,
  nativeAvg*nativeA+(nativeRaw 1142).2.2,
  nativeAvg*nativeA+(nativeRaw 1143).2.2,
  nativeAvg*nativeA+(nativeRaw 1144).2.2,
  nativeAvg*nativeA+(nativeRaw 1145).2.2,
  nativeAvg*nativeA+(nativeRaw 1146).2.2,
  nativeAvg*nativeA+(nativeRaw 1147).2.2,
  nativeAvg*nativeA+(nativeRaw 1148).2.2,
  nativeAvg*nativeA+(nativeRaw 1149).2.2,
  nativeAvg*nativeA+(nativeRaw 1150).2.2,
  nativeAvg*nativeA+(nativeRaw 1151).2.2,
  nativeAvg*nativeA+(nativeRaw 1152).2.2,
  nativeAvg*nativeA+(nativeRaw 1153).2.2,
  nativeAvg*nativeA+(nativeRaw 1154).2.2,
  nativeAvg*nativeA+(nativeRaw 1155).2.2,
  nativeAvg*nativeA+(nativeRaw 1156).2.2,
  nativeAvg*nativeA+(nativeRaw 1157).2.2,
  nativeAvg*nativeA+(nativeRaw 1158).2.2,
  nativeAvg*nativeA+(nativeRaw 1159).2.2,
  nativeAvg*nativeA+(nativeRaw 1160).2.2,
  nativeAvg*nativeA+(nativeRaw 1161).2.2,
  nativeAvg*nativeA+(nativeRaw 1162).2.2,
  nativeAvg*nativeA+(nativeRaw 1163).2.2,
  nativeAvg*nativeA+(nativeRaw 1164).2.2,
  nativeAvg*nativeA+(nativeRaw 1165).2.2,
  nativeAvg*nativeA+(nativeRaw 1166).2.2,
  nativeAvg*nativeA+(nativeRaw 1167).2.2,
  nativeAvg*nativeA+(nativeRaw 1168).2.2
]

def nativeHistoryBuffer1088Start : ℚ × ℚ := ((6804289553110428999847/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457272151312315215234629553978297/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer1088End : ℚ × ℚ := ((13952781744151882573/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457369108240832495855486258029379/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer1088Inputs_length : nativeHistoryBuffer1088Inputs.length = 32 := rfl

theorem nativeHistoryBuffer1088Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1137+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1137+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer1088Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer1088Inputs.getD i.val 0)*(nativeHistoryBuffer1088Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer1088_checked : nativeHistorySteps 49 1088 32 nativeHistoryBuffer1088Inputs nativeHistoryBuffer1088Start = nativeHistoryBuffer1088End := by
  decide +kernel

theorem nativeHistoryBuffer1088Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer1088Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer1088Weight : nativeHistoryRatio^1088 ≤ nativeHistoryBuffer1088Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer1088Real_bound : nativeHistoryReal 49 1088 nativeHistoryBuffer1088Inputs ≤ (nativeHistoryBuffer1088End.2 : ℝ)-(nativeHistoryBuffer1088Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer1088Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer1088Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer1088Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer1088Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer1088Inputs.length) := nativeHistoryBuffer1088Domains ⟨i,by simpa only [nativeHistoryBuffer1088Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer1088Inputs.length) := nativeHistoryBuffer1088Roots ⟨i,by simpa only [nativeHistoryBuffer1088Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer1088Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 1088 nativeHistoryBuffer1088Inputs nativeHistoryBuffer1088Start ht hd hr hw
  simpa only [nativeHistoryBuffer1088Inputs_length,nativeHistoryBuffer1088_checked] using hs

end ASDExplicitGamma.Numerics.Native
