module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0992Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 1001).2.2,
  nativeAvg*nativeA+(nativeRaw 1002).2.2,
  nativeAvg*nativeA+(nativeRaw 1003).2.2,
  nativeAvg*nativeA+(nativeRaw 1004).2.2,
  nativeAvg*nativeA+(nativeRaw 1005).2.2,
  nativeAvg*nativeA+(nativeRaw 1006).2.2,
  nativeAvg*nativeA+(nativeRaw 1007).2.2,
  nativeAvg*nativeA+(nativeRaw 1008).2.2,
  nativeAvg*nativeA+(nativeRaw 1009).2.2,
  nativeAvg*nativeA+(nativeRaw 1010).2.2,
  nativeAvg*nativeA+(nativeRaw 1011).2.2,
  nativeAvg*nativeA+(nativeRaw 1012).2.2,
  nativeAvg*nativeA+(nativeRaw 1013).2.2,
  nativeAvg*nativeA+(nativeRaw 1014).2.2,
  nativeAvg*nativeA+(nativeRaw 1015).2.2,
  nativeAvg*nativeA+(nativeRaw 1016).2.2,
  nativeAvg*nativeA+(nativeRaw 1017).2.2,
  nativeAvg*nativeA+(nativeRaw 1018).2.2,
  nativeAvg*nativeA+(nativeRaw 1019).2.2,
  nativeAvg*nativeA+(nativeRaw 1020).2.2,
  nativeAvg*nativeA+(nativeRaw 1021).2.2,
  nativeAvg*nativeA+(nativeRaw 1022).2.2,
  nativeAvg*nativeA+(nativeRaw 1023).2.2,
  nativeAvg*nativeA+(nativeRaw 1024).2.2,
  nativeAvg*nativeA+(nativeRaw 1025).2.2,
  nativeAvg*nativeA+(nativeRaw 1026).2.2,
  nativeAvg*nativeA+(nativeRaw 1027).2.2,
  nativeAvg*nativeA+(nativeRaw 1028).2.2,
  nativeAvg*nativeA+(nativeRaw 1029).2.2,
  nativeAvg*nativeA+(nativeRaw 1030).2.2,
  nativeAvg*nativeA+(nativeRaw 1031).2.2,
  nativeAvg*nativeA+(nativeRaw 1032).2.2
]

def nativeHistoryStrong0992Start : ℚ × ℚ := ((101008684060816298614863785309/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323501807132359915884908865523897972091/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0992End : ℚ × ℚ := ((32363594684554288114671461/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395447197398197473820201002460466636359830908566007063531533757008473220892427/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0992Inputs_length : nativeHistoryStrong0992Inputs.length = 32 := rfl

theorem nativeHistoryStrong0992Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(1001+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(1001+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0992Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0992Inputs.getD i.val 0)*(nativeHistoryStrong0992Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0992_checked : nativeHistorySteps 9 992 32 nativeHistoryStrong0992Inputs nativeHistoryStrong0992Start = nativeHistoryStrong0992End := by
  decide +kernel

theorem nativeHistoryStrong0992Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0992Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0992Weight : nativeHistoryRatio^992 ≤ nativeHistoryStrong0992Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0992Real_bound : nativeHistoryReal 9 992 nativeHistoryStrong0992Inputs ≤ (nativeHistoryStrong0992End.2 : ℝ)-(nativeHistoryStrong0992Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0992Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0992Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0992Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0992Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0992Inputs.length) := nativeHistoryStrong0992Domains ⟨i,by simpa only [nativeHistoryStrong0992Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0992Inputs.length) := nativeHistoryStrong0992Roots ⟨i,by simpa only [nativeHistoryStrong0992Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0992Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 992 nativeHistoryStrong0992Inputs nativeHistoryStrong0992Start ht hd hr hw
  simpa only [nativeHistoryStrong0992Inputs_length,nativeHistoryStrong0992_checked] using hs

end ASDExplicitGamma.Numerics.Native
