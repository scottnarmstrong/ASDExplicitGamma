module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong1120Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1129).2.2,
  nativeAvg*nativeA+(nativeRaw 1130).2.2,
  nativeAvg*nativeA+(nativeRaw 1131).2.2,
  nativeAvg*nativeA+(nativeRaw 1132).2.2,
  nativeAvg*nativeA+(nativeRaw 1133).2.2,
  nativeAvg*nativeA+(nativeRaw 1134).2.2,
  nativeAvg*nativeA+(nativeRaw 1135).2.2,
  nativeAvg*nativeA+(nativeRaw 1136).2.2,
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
  nativeAvg*nativeA+(nativeRaw 1160).2.2
]

def nativeHistoryStrong1120Start : ℚ × ℚ := ((13952781744151882573/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323635215132080576513121052813368482361/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong1120End : ℚ × ℚ := ((178821129010214211/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323635215132518310011202840425977166111/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong1120Inputs_length : nativeHistoryStrong1120Inputs.length = 32 := rfl

theorem nativeHistoryStrong1120Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1129+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1129+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong1120Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong1120Inputs.getD i.val 0)*(nativeHistoryStrong1120Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong1120_checked : nativeHistorySteps 9 1120 32 nativeHistoryStrong1120Inputs nativeHistoryStrong1120Start = nativeHistoryStrong1120End := by
  decide +kernel

theorem nativeHistoryStrong1120Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong1120Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong1120Weight : nativeHistoryRatio^1120 ≤ nativeHistoryStrong1120Start.1 := by
  decide +kernel

theorem nativeHistoryStrong1120Real_bound : nativeHistoryReal 9 1120 nativeHistoryStrong1120Inputs ≤ (nativeHistoryStrong1120End.2 : ℝ)-(nativeHistoryStrong1120Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong1120Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong1120Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong1120Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong1120Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong1120Inputs.length) := nativeHistoryStrong1120Domains ⟨i,by simpa only [nativeHistoryStrong1120Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong1120Inputs.length) := nativeHistoryStrong1120Roots ⟨i,by simpa only [nativeHistoryStrong1120Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong1120Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 1120 nativeHistoryStrong1120Inputs nativeHistoryStrong1120Start ht hd hr hw
  simpa only [nativeHistoryStrong1120Inputs_length,nativeHistoryStrong1120_checked] using hs

end ASDExplicitGamma.Numerics.Native
