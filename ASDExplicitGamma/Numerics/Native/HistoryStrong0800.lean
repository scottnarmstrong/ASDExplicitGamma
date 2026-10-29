module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0800Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 809).2.2,
  nativeAvg*nativeA+(nativeRaw 810).2.2,
  nativeAvg*nativeA+(nativeRaw 811).2.2,
  nativeAvg*nativeA+(nativeRaw 812).2.2,
  nativeAvg*nativeA+(nativeRaw 813).2.2,
  nativeAvg*nativeA+(nativeRaw 814).2.2,
  nativeAvg*nativeA+(nativeRaw 815).2.2,
  nativeAvg*nativeA+(nativeRaw 816).2.2,
  nativeAvg*nativeA+(nativeRaw 817).2.2,
  nativeAvg*nativeA+(nativeRaw 818).2.2,
  nativeAvg*nativeA+(nativeRaw 819).2.2,
  nativeAvg*nativeA+(nativeRaw 820).2.2,
  nativeAvg*nativeA+(nativeRaw 821).2.2,
  nativeAvg*nativeA+(nativeRaw 822).2.2,
  nativeAvg*nativeA+(nativeRaw 823).2.2,
  nativeAvg*nativeA+(nativeRaw 824).2.2,
  nativeAvg*nativeA+(nativeRaw 825).2.2,
  nativeAvg*nativeA+(nativeRaw 826).2.2,
  nativeAvg*nativeA+(nativeRaw 827).2.2,
  nativeAvg*nativeA+(nativeRaw 828).2.2,
  nativeAvg*nativeA+(nativeRaw 829).2.2,
  nativeAvg*nativeA+(nativeRaw 830).2.2,
  nativeAvg*nativeA+(nativeRaw 831).2.2,
  nativeAvg*nativeA+(nativeRaw 832).2.2,
  nativeAvg*nativeA+(nativeRaw 833).2.2,
  nativeAvg*nativeA+(nativeRaw 834).2.2,
  nativeAvg*nativeA+(nativeRaw 835).2.2,
  nativeAvg*nativeA+(nativeRaw 836).2.2,
  nativeAvg*nativeA+(nativeRaw 837).2.2,
  nativeAvg*nativeA+(nativeRaw 838).2.2,
  nativeAvg*nativeA+(nativeRaw 839).2.2,
  nativeAvg*nativeA+(nativeRaw 840).2.2
]

def nativeHistoryStrong0800Start : ℚ × ℚ := ((1391203250801999705329508869525379513380709/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009840272809242789049253300839235915662872578114489903/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0800End : ℚ × ℚ := ((1141112832937658760071440520171253214589/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841856397505193873648975238140618786122764739197179/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0800Inputs_length : nativeHistoryStrong0800Inputs.length = 32 := rfl

theorem nativeHistoryStrong0800Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(809+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(809+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0800Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0800Inputs.getD i.val 0)*(nativeHistoryStrong0800Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0800_checked : nativeHistorySteps 9 800 32 nativeHistoryStrong0800Inputs nativeHistoryStrong0800Start = nativeHistoryStrong0800End := by
  decide +kernel

theorem nativeHistoryStrong0800Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0800Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0800Weight : nativeHistoryRatio^800 ≤ nativeHistoryStrong0800Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0800Real_bound : nativeHistoryReal 9 800 nativeHistoryStrong0800Inputs ≤ (nativeHistoryStrong0800End.2 : ℝ)-(nativeHistoryStrong0800Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0800Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0800Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0800Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0800Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0800Inputs.length) := nativeHistoryStrong0800Domains ⟨i,by simpa only [nativeHistoryStrong0800Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0800Inputs.length) := nativeHistoryStrong0800Roots ⟨i,by simpa only [nativeHistoryStrong0800Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0800Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 800 nativeHistoryStrong0800Inputs nativeHistoryStrong0800Start ht hd hr hw
  simpa only [nativeHistoryStrong0800Inputs_length,nativeHistoryStrong0800_checked] using hs

end ASDExplicitGamma.Numerics.Native
