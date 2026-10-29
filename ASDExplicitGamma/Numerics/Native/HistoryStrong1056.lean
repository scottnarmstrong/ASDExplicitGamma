module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong1056Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1065).2.2,
  nativeAvg*nativeA+(nativeRaw 1066).2.2,
  nativeAvg*nativeA+(nativeRaw 1067).2.2,
  nativeAvg*nativeA+(nativeRaw 1068).2.2,
  nativeAvg*nativeA+(nativeRaw 1069).2.2,
  nativeAvg*nativeA+(nativeRaw 1070).2.2,
  nativeAvg*nativeA+(nativeRaw 1071).2.2,
  nativeAvg*nativeA+(nativeRaw 1072).2.2,
  nativeAvg*nativeA+(nativeRaw 1073).2.2,
  nativeAvg*nativeA+(nativeRaw 1074).2.2,
  nativeAvg*nativeA+(nativeRaw 1075).2.2,
  nativeAvg*nativeA+(nativeRaw 1076).2.2,
  nativeAvg*nativeA+(nativeRaw 1077).2.2,
  nativeAvg*nativeA+(nativeRaw 1078).2.2,
  nativeAvg*nativeA+(nativeRaw 1079).2.2,
  nativeAvg*nativeA+(nativeRaw 1080).2.2,
  nativeAvg*nativeA+(nativeRaw 1081).2.2,
  nativeAvg*nativeA+(nativeRaw 1082).2.2,
  nativeAvg*nativeA+(nativeRaw 1083).2.2,
  nativeAvg*nativeA+(nativeRaw 1084).2.2,
  nativeAvg*nativeA+(nativeRaw 1085).2.2,
  nativeAvg*nativeA+(nativeRaw 1086).2.2,
  nativeAvg*nativeA+(nativeRaw 1087).2.2,
  nativeAvg*nativeA+(nativeRaw 1088).2.2,
  nativeAvg*nativeA+(nativeRaw 1089).2.2,
  nativeAvg*nativeA+(nativeRaw 1090).2.2,
  nativeAvg*nativeA+(nativeRaw 1091).2.2,
  nativeAvg*nativeA+(nativeRaw 1092).2.2,
  nativeAvg*nativeA+(nativeRaw 1093).2.2,
  nativeAvg*nativeA+(nativeRaw 1094).2.2,
  nativeAvg*nativeA+(nativeRaw 1095).2.2,
  nativeAvg*nativeA+(nativeRaw 1096).2.2
]

def nativeHistoryStrong1056Start : ℚ × ℚ := ((165910845491340978396069/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323635208113409683509923227496294529371/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong1056End : ℚ × ℚ := ((6804289553110428999847/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323635215078408265624400083216130828933/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong1056Inputs_length : nativeHistoryStrong1056Inputs.length = 32 := rfl

theorem nativeHistoryStrong1056Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1065+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1065+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong1056Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong1056Inputs.getD i.val 0)*(nativeHistoryStrong1056Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong1056_checked : nativeHistorySteps 9 1056 32 nativeHistoryStrong1056Inputs nativeHistoryStrong1056Start = nativeHistoryStrong1056End := by
  decide +kernel

theorem nativeHistoryStrong1056Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong1056Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong1056Weight : nativeHistoryRatio^1056 ≤ nativeHistoryStrong1056Start.1 := by
  decide +kernel

theorem nativeHistoryStrong1056Real_bound : nativeHistoryReal 9 1056 nativeHistoryStrong1056Inputs ≤ (nativeHistoryStrong1056End.2 : ℝ)-(nativeHistoryStrong1056Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong1056Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong1056Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong1056Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong1056Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong1056Inputs.length) := nativeHistoryStrong1056Domains ⟨i,by simpa only [nativeHistoryStrong1056Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong1056Inputs.length) := nativeHistoryStrong1056Roots ⟨i,by simpa only [nativeHistoryStrong1056Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong1056Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 1056 nativeHistoryStrong1056Inputs nativeHistoryStrong1056Start ht hd hr hw
  simpa only [nativeHistoryStrong1056Inputs_length,nativeHistoryStrong1056_checked] using hs

end ASDExplicitGamma.Numerics.Native
