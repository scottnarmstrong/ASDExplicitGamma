module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0192Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 241).2.2,
  nativeAvg*nativeA+(nativeRaw 242).2.2,
  nativeAvg*nativeA+(nativeRaw 243).2.2,
  nativeAvg*nativeA+(nativeRaw 244).2.2,
  nativeAvg*nativeA+(nativeRaw 245).2.2,
  nativeAvg*nativeA+(nativeRaw 246).2.2,
  nativeAvg*nativeA+(nativeRaw 247).2.2,
  nativeAvg*nativeA+(nativeRaw 248).2.2,
  nativeAvg*nativeA+(nativeRaw 249).2.2,
  nativeAvg*nativeA+(nativeRaw 250).2.2,
  nativeAvg*nativeA+(nativeRaw 251).2.2,
  nativeAvg*nativeA+(nativeRaw 252).2.2,
  nativeAvg*nativeA+(nativeRaw 253).2.2,
  nativeAvg*nativeA+(nativeRaw 254).2.2,
  nativeAvg*nativeA+(nativeRaw 255).2.2,
  nativeAvg*nativeA+(nativeRaw 256).2.2,
  nativeAvg*nativeA+(nativeRaw 257).2.2,
  nativeAvg*nativeA+(nativeRaw 258).2.2,
  nativeAvg*nativeA+(nativeRaw 259).2.2,
  nativeAvg*nativeA+(nativeRaw 260).2.2,
  nativeAvg*nativeA+(nativeRaw 261).2.2,
  nativeAvg*nativeA+(nativeRaw 262).2.2,
  nativeAvg*nativeA+(nativeRaw 263).2.2,
  nativeAvg*nativeA+(nativeRaw 264).2.2,
  nativeAvg*nativeA+(nativeRaw 265).2.2,
  nativeAvg*nativeA+(nativeRaw 266).2.2,
  nativeAvg*nativeA+(nativeRaw 267).2.2,
  nativeAvg*nativeA+(nativeRaw 268).2.2,
  nativeAvg*nativeA+(nativeRaw 269).2.2,
  nativeAvg*nativeA+(nativeRaw 270).2.2,
  nativeAvg*nativeA+(nativeRaw 271).2.2,
  nativeAvg*nativeA+(nativeRaw 272).2.2
]

def nativeHistoryBuffer0192Start : ℚ × ℚ := ((181513168551372517887327554474984065058856330600436355648770249424640774868317387849983/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161850230730741795640998286555843913823562583821042090208825371490437851659925525837371900561867/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0192End : ℚ × ℚ := ((93052096207789479157517473621490049532302614606852871241834371373282060612229103427/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703379091308058146291834339383757272147536151366262960575599059102132445134763317608918640131/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0192Inputs_length : nativeHistoryBuffer0192Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0192Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(241+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(241+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0192Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0192Inputs.getD i.val 0)*(nativeHistoryBuffer0192Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0192_checked : nativeHistorySteps 49 192 32 nativeHistoryBuffer0192Inputs nativeHistoryBuffer0192Start = nativeHistoryBuffer0192End := by
  decide +kernel

theorem nativeHistoryBuffer0192Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0192Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0192Weight : nativeHistoryRatio^192 ≤ nativeHistoryBuffer0192Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0192Real_bound : nativeHistoryReal 49 192 nativeHistoryBuffer0192Inputs ≤ (nativeHistoryBuffer0192End.2 : ℝ)-(nativeHistoryBuffer0192Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0192Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0192Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0192Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0192Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0192Inputs.length) := nativeHistoryBuffer0192Domains ⟨i,by simpa only [nativeHistoryBuffer0192Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0192Inputs.length) := nativeHistoryBuffer0192Roots ⟨i,by simpa only [nativeHistoryBuffer0192Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0192Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 192 nativeHistoryBuffer0192Inputs nativeHistoryBuffer0192Start ht hd hr hw
  simpa only [nativeHistoryBuffer0192Inputs_length,nativeHistoryBuffer0192_checked] using hs

end ASDExplicitGamma.Numerics.Native
