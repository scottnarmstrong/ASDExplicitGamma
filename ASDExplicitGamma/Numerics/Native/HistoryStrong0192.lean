module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0192Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 201).2.2,
  nativeAvg*nativeA+(nativeRaw 202).2.2,
  nativeAvg*nativeA+(nativeRaw 203).2.2,
  nativeAvg*nativeA+(nativeRaw 204).2.2,
  nativeAvg*nativeA+(nativeRaw 205).2.2,
  nativeAvg*nativeA+(nativeRaw 206).2.2,
  nativeAvg*nativeA+(nativeRaw 207).2.2,
  nativeAvg*nativeA+(nativeRaw 208).2.2,
  nativeAvg*nativeA+(nativeRaw 209).2.2,
  nativeAvg*nativeA+(nativeRaw 210).2.2,
  nativeAvg*nativeA+(nativeRaw 211).2.2,
  nativeAvg*nativeA+(nativeRaw 212).2.2,
  nativeAvg*nativeA+(nativeRaw 213).2.2,
  nativeAvg*nativeA+(nativeRaw 214).2.2,
  nativeAvg*nativeA+(nativeRaw 215).2.2,
  nativeAvg*nativeA+(nativeRaw 216).2.2,
  nativeAvg*nativeA+(nativeRaw 217).2.2,
  nativeAvg*nativeA+(nativeRaw 218).2.2,
  nativeAvg*nativeA+(nativeRaw 219).2.2,
  nativeAvg*nativeA+(nativeRaw 220).2.2,
  nativeAvg*nativeA+(nativeRaw 221).2.2,
  nativeAvg*nativeA+(nativeRaw 222).2.2,
  nativeAvg*nativeA+(nativeRaw 223).2.2,
  nativeAvg*nativeA+(nativeRaw 224).2.2,
  nativeAvg*nativeA+(nativeRaw 225).2.2,
  nativeAvg*nativeA+(nativeRaw 226).2.2,
  nativeAvg*nativeA+(nativeRaw 227).2.2,
  nativeAvg*nativeA+(nativeRaw 228).2.2,
  nativeAvg*nativeA+(nativeRaw 229).2.2,
  nativeAvg*nativeA+(nativeRaw 230).2.2,
  nativeAvg*nativeA+(nativeRaw 231).2.2,
  nativeAvg*nativeA+(nativeRaw 232).2.2
]

def nativeHistoryStrong0192Start : ℚ × ℚ := ((181513168551372517887327554474984065058856330600436355648770249424640774868317387849983/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062655905000160285524296261777880575556547264881703762844561688798777887836794228209613340889709/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0192End : ℚ × ℚ := ((93052096207789479157517473621490049532302614606852871241834371373282060612229103427/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(1189382832293532302815371273341519299289762448920477011587896703207326552834840664016783823942753193/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0192Inputs_length : nativeHistoryStrong0192Inputs.length = 32 := rfl

theorem nativeHistoryStrong0192Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(201+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(201+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0192Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0192Inputs.getD i.val 0)*(nativeHistoryStrong0192Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0192_checked : nativeHistorySteps 9 192 32 nativeHistoryStrong0192Inputs nativeHistoryStrong0192Start = nativeHistoryStrong0192End := by
  decide +kernel

theorem nativeHistoryStrong0192Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0192Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0192Weight : nativeHistoryRatio^192 ≤ nativeHistoryStrong0192Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0192Real_bound : nativeHistoryReal 9 192 nativeHistoryStrong0192Inputs ≤ (nativeHistoryStrong0192End.2 : ℝ)-(nativeHistoryStrong0192Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0192Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0192Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0192Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0192Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0192Inputs.length) := nativeHistoryStrong0192Domains ⟨i,by simpa only [nativeHistoryStrong0192Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0192Inputs.length) := nativeHistoryStrong0192Roots ⟨i,by simpa only [nativeHistoryStrong0192Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0192Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 192 nativeHistoryStrong0192Inputs nativeHistoryStrong0192Start ht hd hr hw
  simpa only [nativeHistoryStrong0192Inputs_length,nativeHistoryStrong0192_checked] using hs

end ASDExplicitGamma.Numerics.Native
