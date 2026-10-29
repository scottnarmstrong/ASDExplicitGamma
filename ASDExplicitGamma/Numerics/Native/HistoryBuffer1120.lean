module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer1120Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1169).2.2,
  nativeAvg*nativeA+(nativeRaw 1170).2.2,
  nativeAvg*nativeA+(nativeRaw 1171).2.2,
  nativeAvg*nativeA+(nativeRaw 1172).2.2,
  nativeAvg*nativeA+(nativeRaw 1173).2.2,
  nativeAvg*nativeA+(nativeRaw 1174).2.2,
  nativeAvg*nativeA+(nativeRaw 1175).2.2,
  nativeAvg*nativeA+(nativeRaw 1176).2.2,
  nativeAvg*nativeA+(nativeRaw 1177).2.2,
  nativeAvg*nativeA+(nativeRaw 1178).2.2,
  nativeAvg*nativeA+(nativeRaw 1179).2.2,
  nativeAvg*nativeA+(nativeRaw 1180).2.2,
  nativeAvg*nativeA+(nativeRaw 1181).2.2,
  nativeAvg*nativeA+(nativeRaw 1182).2.2,
  nativeAvg*nativeA+(nativeRaw 1183).2.2,
  nativeAvg*nativeA+(nativeRaw 1184).2.2,
  nativeAvg*nativeA+(nativeRaw 1185).2.2,
  nativeAvg*nativeA+(nativeRaw 1186).2.2,
  nativeAvg*nativeA+(nativeRaw 1187).2.2,
  nativeAvg*nativeA+(nativeRaw 1188).2.2,
  nativeAvg*nativeA+(nativeRaw 1189).2.2,
  nativeAvg*nativeA+(nativeRaw 1190).2.2,
  nativeAvg*nativeA+(nativeRaw 1191).2.2,
  nativeAvg*nativeA+(nativeRaw 1192).2.2,
  nativeAvg*nativeA+(nativeRaw 1193).2.2,
  nativeAvg*nativeA+(nativeRaw 1194).2.2,
  nativeAvg*nativeA+(nativeRaw 1195).2.2,
  nativeAvg*nativeA+(nativeRaw 1196).2.2,
  nativeAvg*nativeA+(nativeRaw 1197).2.2,
  nativeAvg*nativeA+(nativeRaw 1198).2.2,
  nativeAvg*nativeA+(nativeRaw 1199).2.2,
  nativeAvg*nativeA+(nativeRaw 1200).2.2
]

def nativeHistoryBuffer1120Start : ℚ × ℚ := ((13952781744151882573/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366935001193457369108240832495855486258029379/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer1120End : ℚ × ℚ := ((178821129010214211/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(14641580925849106226701415786384343621134619778273363930341733750298364342495638655187170719060774311/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer1120Inputs_length : nativeHistoryBuffer1120Inputs.length = 32 := rfl

theorem nativeHistoryBuffer1120Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1169+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1169+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer1120Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer1120Inputs.getD i.val 0)*(nativeHistoryBuffer1120Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer1120_checked : nativeHistorySteps 49 1120 32 nativeHistoryBuffer1120Inputs nativeHistoryBuffer1120Start = nativeHistoryBuffer1120End := by
  decide +kernel

theorem nativeHistoryBuffer1120Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer1120Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer1120Weight : nativeHistoryRatio^1120 ≤ nativeHistoryBuffer1120Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer1120Real_bound : nativeHistoryReal 49 1120 nativeHistoryBuffer1120Inputs ≤ (nativeHistoryBuffer1120End.2 : ℝ)-(nativeHistoryBuffer1120Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer1120Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer1120Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer1120Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer1120Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer1120Inputs.length) := nativeHistoryBuffer1120Domains ⟨i,by simpa only [nativeHistoryBuffer1120Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer1120Inputs.length) := nativeHistoryBuffer1120Roots ⟨i,by simpa only [nativeHistoryBuffer1120Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer1120Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 1120 nativeHistoryBuffer1120Inputs nativeHistoryBuffer1120Start ht hd hr hw
  simpa only [nativeHistoryBuffer1120Inputs_length,nativeHistoryBuffer1120_checked] using hs

end ASDExplicitGamma.Numerics.Native
