module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0320Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 369).2.2,
  nativeAvg*nativeA+(nativeRaw 370).2.2,
  nativeAvg*nativeA+(nativeRaw 371).2.2,
  nativeAvg*nativeA+(nativeRaw 372).2.2,
  nativeAvg*nativeA+(nativeRaw 373).2.2,
  nativeAvg*nativeA+(nativeRaw 374).2.2,
  nativeAvg*nativeA+(nativeRaw 375).2.2,
  nativeAvg*nativeA+(nativeRaw 376).2.2,
  nativeAvg*nativeA+(nativeRaw 377).2.2,
  nativeAvg*nativeA+(nativeRaw 378).2.2,
  nativeAvg*nativeA+(nativeRaw 379).2.2,
  nativeAvg*nativeA+(nativeRaw 380).2.2,
  nativeAvg*nativeA+(nativeRaw 381).2.2,
  nativeAvg*nativeA+(nativeRaw 382).2.2,
  nativeAvg*nativeA+(nativeRaw 383).2.2,
  nativeAvg*nativeA+(nativeRaw 384).2.2,
  nativeAvg*nativeA+(nativeRaw 385).2.2,
  nativeAvg*nativeA+(nativeRaw 386).2.2,
  nativeAvg*nativeA+(nativeRaw 387).2.2,
  nativeAvg*nativeA+(nativeRaw 388).2.2,
  nativeAvg*nativeA+(nativeRaw 389).2.2,
  nativeAvg*nativeA+(nativeRaw 390).2.2,
  nativeAvg*nativeA+(nativeRaw 391).2.2,
  nativeAvg*nativeA+(nativeRaw 392).2.2,
  nativeAvg*nativeA+(nativeRaw 393).2.2,
  nativeAvg*nativeA+(nativeRaw 394).2.2,
  nativeAvg*nativeA+(nativeRaw 395).2.2,
  nativeAvg*nativeA+(nativeRaw 396).2.2,
  nativeAvg*nativeA+(nativeRaw 397).2.2,
  nativeAvg*nativeA+(nativeRaw 398).2.2,
  nativeAvg*nativeA+(nativeRaw 399).2.2,
  nativeAvg*nativeA+(nativeRaw 400).2.2
]

def nativeHistoryBuffer0320Start : ℚ × ℚ := ((31341533255718553419973577425489141501976444891534968914217777178128571746269/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424903226370149056819699213827747419339208971146938831130435243352762033698162710698657/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0320End : ℚ × ℚ := ((321342566061299008933678526379079320826925598699175936907128355535521426413/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453392230573216967306548364630500781585176137167428818185918500272200065223891004483/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0320Inputs_length : nativeHistoryBuffer0320Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0320Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(369+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(369+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0320Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0320Inputs.getD i.val 0)*(nativeHistoryBuffer0320Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0320_checked : nativeHistorySteps 49 320 32 nativeHistoryBuffer0320Inputs nativeHistoryBuffer0320Start = nativeHistoryBuffer0320End := by
  decide +kernel

theorem nativeHistoryBuffer0320Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0320Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0320Weight : nativeHistoryRatio^320 ≤ nativeHistoryBuffer0320Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0320Real_bound : nativeHistoryReal 49 320 nativeHistoryBuffer0320Inputs ≤ (nativeHistoryBuffer0320End.2 : ℝ)-(nativeHistoryBuffer0320Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0320Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0320Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0320Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0320Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0320Inputs.length) := nativeHistoryBuffer0320Domains ⟨i,by simpa only [nativeHistoryBuffer0320Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0320Inputs.length) := nativeHistoryBuffer0320Roots ⟨i,by simpa only [nativeHistoryBuffer0320Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0320Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 320 nativeHistoryBuffer0320Inputs nativeHistoryBuffer0320Start ht hd hr hw
  simpa only [nativeHistoryBuffer0320Inputs_length,nativeHistoryBuffer0320_checked] using hs

end ASDExplicitGamma.Numerics.Native
