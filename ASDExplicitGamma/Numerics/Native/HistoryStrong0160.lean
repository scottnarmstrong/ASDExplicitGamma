module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0160Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 169).2.2,
  nativeAvg*nativeA+(nativeRaw 170).2.2,
  nativeAvg*nativeA+(nativeRaw 171).2.2,
  nativeAvg*nativeA+(nativeRaw 172).2.2,
  nativeAvg*nativeA+(nativeRaw 173).2.2,
  nativeAvg*nativeA+(nativeRaw 174).2.2,
  nativeAvg*nativeA+(nativeRaw 175).2.2,
  nativeAvg*nativeA+(nativeRaw 176).2.2,
  nativeAvg*nativeA+(nativeRaw 177).2.2,
  nativeAvg*nativeA+(nativeRaw 178).2.2,
  nativeAvg*nativeA+(nativeRaw 179).2.2,
  nativeAvg*nativeA+(nativeRaw 180).2.2,
  nativeAvg*nativeA+(nativeRaw 181).2.2,
  nativeAvg*nativeA+(nativeRaw 182).2.2,
  nativeAvg*nativeA+(nativeRaw 183).2.2,
  nativeAvg*nativeA+(nativeRaw 184).2.2,
  nativeAvg*nativeA+(nativeRaw 185).2.2,
  nativeAvg*nativeA+(nativeRaw 186).2.2,
  nativeAvg*nativeA+(nativeRaw 187).2.2,
  nativeAvg*nativeA+(nativeRaw 188).2.2,
  nativeAvg*nativeA+(nativeRaw 189).2.2,
  nativeAvg*nativeA+(nativeRaw 190).2.2,
  nativeAvg*nativeA+(nativeRaw 191).2.2,
  nativeAvg*nativeA+(nativeRaw 192).2.2,
  nativeAvg*nativeA+(nativeRaw 193).2.2,
  nativeAvg*nativeA+(nativeRaw 194).2.2,
  nativeAvg*nativeA+(nativeRaw 195).2.2,
  nativeAvg*nativeA+(nativeRaw 196).2.2,
  nativeAvg*nativeA+(nativeRaw 197).2.2,
  nativeAvg*nativeA+(nativeRaw 198).2.2,
  nativeAvg*nativeA+(nativeRaw 199).2.2,
  nativeAvg*nativeA+(nativeRaw 200).2.2
]

def nativeHistoryStrong0160Start : ℚ × ℚ := ((1416283209095549299797276381654664966001910515183972732739379003373390715312677559085997/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757531121400334977404125557484728141237665600545353473043247240440338419702326395938384565629818439/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0160End : ℚ × ℚ := ((181513168551372517887327554474984065058856330600436355648770249424640774868317387849983/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062655905000160285524296261777880575556547264881703762844561688798777887836794228209613340889709/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0160Inputs_length : nativeHistoryStrong0160Inputs.length = 32 := rfl

theorem nativeHistoryStrong0160Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(169+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(169+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0160Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0160Inputs.getD i.val 0)*(nativeHistoryStrong0160Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0160_checked : nativeHistorySteps 9 160 32 nativeHistoryStrong0160Inputs nativeHistoryStrong0160Start = nativeHistoryStrong0160End := by
  decide +kernel

theorem nativeHistoryStrong0160Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0160Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0160Weight : nativeHistoryRatio^160 ≤ nativeHistoryStrong0160Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0160Real_bound : nativeHistoryReal 9 160 nativeHistoryStrong0160Inputs ≤ (nativeHistoryStrong0160End.2 : ℝ)-(nativeHistoryStrong0160Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0160Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0160Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0160Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0160Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0160Inputs.length) := nativeHistoryStrong0160Domains ⟨i,by simpa only [nativeHistoryStrong0160Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0160Inputs.length) := nativeHistoryStrong0160Roots ⟨i,by simpa only [nativeHistoryStrong0160Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0160Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 160 nativeHistoryStrong0160Inputs nativeHistoryStrong0160Start ht hd hr hw
  simpa only [nativeHistoryStrong0160Inputs_length,nativeHistoryStrong0160_checked] using hs

end ASDExplicitGamma.Numerics.Native
