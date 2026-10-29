module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0160Inputs : List ℚ := [
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
  nativeAvg*nativeA+(nativeRaw 232).2.2,
  nativeAvg*nativeA+(nativeRaw 233).2.2,
  nativeAvg*nativeA+(nativeRaw 234).2.2,
  nativeAvg*nativeA+(nativeRaw 235).2.2,
  nativeAvg*nativeA+(nativeRaw 236).2.2,
  nativeAvg*nativeA+(nativeRaw 237).2.2,
  nativeAvg*nativeA+(nativeRaw 238).2.2,
  nativeAvg*nativeA+(nativeRaw 239).2.2,
  nativeAvg*nativeA+(nativeRaw 240).2.2
]

def nativeHistoryBuffer0160Start : ℚ × ℚ := ((1416283209095549299797276381654664966001910515183972732739379003373390715312677559085997/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161603302352930801240766828889477011683769416126868801618272575763876987870500759329379029183559/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0160End : ℚ × ℚ := ((181513168551372517887327554474984065058856330600436355648770249424640774868317387849983/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161850230730741795640998286555843913823562583821042090208825371490437851659925525837371900561867/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0160Inputs_length : nativeHistoryBuffer0160Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0160Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(209+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(209+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0160Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0160Inputs.getD i.val 0)*(nativeHistoryBuffer0160Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0160_checked : nativeHistorySteps 49 160 32 nativeHistoryBuffer0160Inputs nativeHistoryBuffer0160Start = nativeHistoryBuffer0160End := by
  decide +kernel

theorem nativeHistoryBuffer0160Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0160Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0160Weight : nativeHistoryRatio^160 ≤ nativeHistoryBuffer0160Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0160Real_bound : nativeHistoryReal 49 160 nativeHistoryBuffer0160Inputs ≤ (nativeHistoryBuffer0160End.2 : ℝ)-(nativeHistoryBuffer0160Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0160Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0160Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0160Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0160Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0160Inputs.length) := nativeHistoryBuffer0160Domains ⟨i,by simpa only [nativeHistoryBuffer0160Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0160Inputs.length) := nativeHistoryBuffer0160Roots ⟨i,by simpa only [nativeHistoryBuffer0160Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0160Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 160 nativeHistoryBuffer0160Inputs nativeHistoryBuffer0160Start ht hd hr hw
  simpa only [nativeHistoryBuffer0160Inputs_length,nativeHistoryBuffer0160_checked] using hs

end ASDExplicitGamma.Numerics.Native
