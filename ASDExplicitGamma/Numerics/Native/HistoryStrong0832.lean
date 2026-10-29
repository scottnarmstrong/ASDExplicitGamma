module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0832Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 841).2.2,
  nativeAvg*nativeA+(nativeRaw 842).2.2,
  nativeAvg*nativeA+(nativeRaw 843).2.2,
  nativeAvg*nativeA+(nativeRaw 844).2.2,
  nativeAvg*nativeA+(nativeRaw 845).2.2,
  nativeAvg*nativeA+(nativeRaw 846).2.2,
  nativeAvg*nativeA+(nativeRaw 847).2.2,
  nativeAvg*nativeA+(nativeRaw 848).2.2,
  nativeAvg*nativeA+(nativeRaw 849).2.2,
  nativeAvg*nativeA+(nativeRaw 850).2.2,
  nativeAvg*nativeA+(nativeRaw 851).2.2,
  nativeAvg*nativeA+(nativeRaw 852).2.2,
  nativeAvg*nativeA+(nativeRaw 853).2.2,
  nativeAvg*nativeA+(nativeRaw 854).2.2,
  nativeAvg*nativeA+(nativeRaw 855).2.2,
  nativeAvg*nativeA+(nativeRaw 856).2.2,
  nativeAvg*nativeA+(nativeRaw 857).2.2,
  nativeAvg*nativeA+(nativeRaw 858).2.2,
  nativeAvg*nativeA+(nativeRaw 859).2.2,
  nativeAvg*nativeA+(nativeRaw 860).2.2,
  nativeAvg*nativeA+(nativeRaw 861).2.2,
  nativeAvg*nativeA+(nativeRaw 862).2.2,
  nativeAvg*nativeA+(nativeRaw 863).2.2,
  nativeAvg*nativeA+(nativeRaw 864).2.2,
  nativeAvg*nativeA+(nativeRaw 865).2.2,
  nativeAvg*nativeA+(nativeRaw 866).2.2,
  nativeAvg*nativeA+(nativeRaw 867).2.2,
  nativeAvg*nativeA+(nativeRaw 868).2.2,
  nativeAvg*nativeA+(nativeRaw 869).2.2,
  nativeAvg*nativeA+(nativeRaw 870).2.2,
  nativeAvg*nativeA+(nativeRaw 871).2.2,
  nativeAvg*nativeA+(nativeRaw 872).2.2
]

def nativeHistoryStrong0832Start : ℚ × ℚ := ((1141112832937658760071440520171253214589/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841856397505193873648975238140618786122764739197179/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0832End : ℚ × ℚ := ((146246883851302975226031747223401938681/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866480033755472053348855453256548533180060055691/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0832Inputs_length : nativeHistoryStrong0832Inputs.length = 32 := rfl

theorem nativeHistoryStrong0832Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(841+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(841+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0832Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0832Inputs.getD i.val 0)*(nativeHistoryStrong0832Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0832_checked : nativeHistorySteps 9 832 32 nativeHistoryStrong0832Inputs nativeHistoryStrong0832Start = nativeHistoryStrong0832End := by
  decide +kernel

theorem nativeHistoryStrong0832Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0832Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0832Weight : nativeHistoryRatio^832 ≤ nativeHistoryStrong0832Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0832Real_bound : nativeHistoryReal 9 832 nativeHistoryStrong0832Inputs ≤ (nativeHistoryStrong0832End.2 : ℝ)-(nativeHistoryStrong0832Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0832Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0832Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0832Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0832Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0832Inputs.length) := nativeHistoryStrong0832Domains ⟨i,by simpa only [nativeHistoryStrong0832Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0832Inputs.length) := nativeHistoryStrong0832Roots ⟨i,by simpa only [nativeHistoryStrong0832Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0832Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 832 nativeHistoryStrong0832Inputs nativeHistoryStrong0832Start ht hd hr hw
  simpa only [nativeHistoryStrong0832Inputs_length,nativeHistoryStrong0832_checked] using hs

end ASDExplicitGamma.Numerics.Native
