module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong1088Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1097).2.2,
  nativeAvg*nativeA+(nativeRaw 1098).2.2,
  nativeAvg*nativeA+(nativeRaw 1099).2.2,
  nativeAvg*nativeA+(nativeRaw 1100).2.2,
  nativeAvg*nativeA+(nativeRaw 1101).2.2,
  nativeAvg*nativeA+(nativeRaw 1102).2.2,
  nativeAvg*nativeA+(nativeRaw 1103).2.2,
  nativeAvg*nativeA+(nativeRaw 1104).2.2,
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
  nativeAvg*nativeA+(nativeRaw 1128).2.2
]

def nativeHistoryStrong1088Start : ℚ × ℚ := ((6804289553110428999847/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323635215078408265624400083216130828933/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong1088End : ℚ × ℚ := ((13952781744151882573/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323635215132080576513121052813368482361/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong1088Inputs_length : nativeHistoryStrong1088Inputs.length = 32 := rfl

theorem nativeHistoryStrong1088Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1097+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1097+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong1088Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong1088Inputs.getD i.val 0)*(nativeHistoryStrong1088Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong1088_checked : nativeHistorySteps 9 1088 32 nativeHistoryStrong1088Inputs nativeHistoryStrong1088Start = nativeHistoryStrong1088End := by
  decide +kernel

theorem nativeHistoryStrong1088Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong1088Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong1088Weight : nativeHistoryRatio^1088 ≤ nativeHistoryStrong1088Start.1 := by
  decide +kernel

theorem nativeHistoryStrong1088Real_bound : nativeHistoryReal 9 1088 nativeHistoryStrong1088Inputs ≤ (nativeHistoryStrong1088End.2 : ℝ)-(nativeHistoryStrong1088Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong1088Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong1088Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong1088Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong1088Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong1088Inputs.length) := nativeHistoryStrong1088Domains ⟨i,by simpa only [nativeHistoryStrong1088Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong1088Inputs.length) := nativeHistoryStrong1088Roots ⟨i,by simpa only [nativeHistoryStrong1088Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong1088Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 1088 nativeHistoryStrong1088Inputs nativeHistoryStrong1088Start ht hd hr hw
  simpa only [nativeHistoryStrong1088Inputs_length,nativeHistoryStrong1088_checked] using hs

end ASDExplicitGamma.Numerics.Native
