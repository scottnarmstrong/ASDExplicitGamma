module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0224Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 233).2.2,
  nativeAvg*nativeA+(nativeRaw 234).2.2,
  nativeAvg*nativeA+(nativeRaw 235).2.2,
  nativeAvg*nativeA+(nativeRaw 236).2.2,
  nativeAvg*nativeA+(nativeRaw 237).2.2,
  nativeAvg*nativeA+(nativeRaw 238).2.2,
  nativeAvg*nativeA+(nativeRaw 239).2.2,
  nativeAvg*nativeA+(nativeRaw 240).2.2,
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
  nativeAvg*nativeA+(nativeRaw 264).2.2
]

def nativeHistoryStrong0224Start : ℚ × ℚ := ((93052096207789479157517473621490049532302614606852871241834371373282060612229103427/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(1189382832293532302815371273341519299289762448920477011587896703207326552834840664016783823942753193/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0224End : ℚ × ℚ := ((190811337331992955824335638343396339518377295688766885423290244550061147419680049/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362695086224439502808652794377106165404919645536532488847738239927789047258475231487657409/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0224Inputs_length : nativeHistoryStrong0224Inputs.length = 32 := rfl

theorem nativeHistoryStrong0224Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(233+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(233+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0224Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0224Inputs.getD i.val 0)*(nativeHistoryStrong0224Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0224_checked : nativeHistorySteps 9 224 32 nativeHistoryStrong0224Inputs nativeHistoryStrong0224Start = nativeHistoryStrong0224End := by
  decide +kernel

theorem nativeHistoryStrong0224Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0224Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0224Weight : nativeHistoryRatio^224 ≤ nativeHistoryStrong0224Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0224Real_bound : nativeHistoryReal 9 224 nativeHistoryStrong0224Inputs ≤ (nativeHistoryStrong0224End.2 : ℝ)-(nativeHistoryStrong0224Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0224Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0224Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0224Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0224Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0224Inputs.length) := nativeHistoryStrong0224Domains ⟨i,by simpa only [nativeHistoryStrong0224Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0224Inputs.length) := nativeHistoryStrong0224Roots ⟨i,by simpa only [nativeHistoryStrong0224Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0224Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 224 nativeHistoryStrong0224Inputs nativeHistoryStrong0224Start ht hd hr hw
  simpa only [nativeHistoryStrong0224Inputs_length,nativeHistoryStrong0224_checked] using hs

end ASDExplicitGamma.Numerics.Native
